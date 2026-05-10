# Erdős Problem 42 — Sidon difference avoidance

> [erdosproblems.com/42](https://www.erdosproblems.com/42)
>
> ⚠️ **In progress.** The active public #42 wrapper now uses Route A and no
> longer depends on the compact-Cayley clique axiom. It is conditional on the
> theorem-shaped finite Fourier avoidance count axiom
> `finite_fourier_avoidance_count`; the existence interface used downstream is
> derived from that count statement.
> See
> [§ Current state](#current-state).

For every `M ≥ 1`, every sufficiently large `N`, and every non-empty Sidon set `A ⊆ {1, …, N}`, there is another Sidon set `B ⊆ {1, …, N}` of size `M` with

```
(A − A) ∩ (B − B) = {0}.
```

Erdős's #42, [`[Er95]`]. The active Lean route follows the Fourier-positive /
Green-Tao `U²` route from the Ulam/Tao note: a finite avoidance theorem gives a
large tuple avoiding `A - A`, and the downstream Sidon extraction is finite
combinatorics. The compact-Cayley route remains preserved separately in
`CompactCayley/Main.lean`.

## Files

| File | What |
|------|------|
| [`Proof.lean`](Proof.lean) | Thin modular active-proof alias; currently imports `FC/Shape.lean`. |
| [`FourierPositive/Proof.lean`](FourierPositive/Proof.lean) | Standalone flat Route A bundle: shared machinery + Fourier-positive proof + public wrappers. |
| [`CompactCayley/Proof.lean`](CompactCayley/Proof.lean) | Standalone flat Route B bundle: shared machinery + compact-Cayley proof + axiom audit. |
| [`Shared/Common.lean`](Shared/Common.lean), [`Shared/Sidon.lean`](Shared/Sidon.lean), [`Shared/FiniteFourier.lean`](Shared/FiniteFourier.lean) | Shared finite-combinatorial, Sidon, and normalized `ZMod.dft` API used by both routes. |
| [`Shared/FiniteReduction.lean`](Shared/FiniteReduction.lean) | Route-neutral greedy Sidon, finite Fourier, allowed-difference, and cyclic-interval lemmas. |
| [`Common.lean`](Common.lean), [`Sidon.lean`](Sidon.lean), [`FiniteFourier.lean`](FiniteFourier.lean), [`FiniteReduction.lean`](FiniteReduction.lean) | Compatibility import shims for older module paths; P42 route files import `Shared/*` directly. |
| [`CompactCayley/CliqueAxiom.lean`](CompactCayley/CliqueAxiom.lean) | Proved Route B compact-Cayley clique theorem, `compact_cayley_clique`. |
| [`CompactCayley/CliqueEndpoint.lean`](CompactCayley/CliqueEndpoint.lean) | Finite tuple-to-clique endpoint for opening the compact-Cayley axiom. |
| [`CompactCayley/SpectralCutNorm.lean`](CompactCayley/SpectralCutNorm.lean) | Route B Lemma 2.5 finite spectral layer: Cayley cut functional, Fourier factorization, Parseval, and checked spectral bound for bounded tests. |
| [`CompactCayley/CountingConvergence.lean`](CompactCayley/CountingConvergence.lean) | Finite generic `K_ℓ` density target for Route B Lemma 2.6, linked back to the indicator clique endpoint. |
| [`CompactCayley/PositiveDefinite.lean`](CompactCayley/PositiveDefinite.lean) | Route B Lemma 2.7 endpoint interface: builds the closed proper level-one subgroup and positive continuous clique density from the positive-definite closure property. |
| [`CompactCayley/Main.lean`](CompactCayley/Main.lean) | Route B downstream theorem, isolated behind `compact_cayley_clique`. |
| [`FourierPositive/FiniteAvoidance.lean`](FourierPositive/FiniteAvoidance.lean) | Route A trust boundary, `finite_fourier_avoidance_count`, plus derived existence theorem. |
| [`FourierPositive/Counterexample.lean`](FourierPositive/Counterexample.lean) | Route A contradiction scaffold: explicit-prime theorem shape and counterexample sequence for opening `finite_fourier_avoidance_count`. |
| [`FourierPositive/Counting.lean`](FourierPositive/Counting.lean) | Route A finite weighted pattern-count API and inclusion-exclusion expansion of the avoidance density. |
| [`FourierPositive/Fejer.lean`](FourierPositive/Fejer.lean) | Route A Fejer kernels on the extraction compact dual and finite cyclic lifts. |
| [`FourierPositive/Main.lean`](FourierPositive/Main.lean) | Route A forbidden-set setup, Fourier lower-bound bridge, and downstream theorem. |
| [`CompactCayley/ContinuousEndpoint.lean`](CompactCayley/ContinuousEndpoint.lean) | Continuous Haar/null-set endpoints used when opening the compactness arguments. |
| [`FC/Local.lean`](FC/Local.lean) | Public `Set ℕ` theorem and FC-style `erdos_42` wrapper. |
| [`FC/Shape.lean`](FC/Shape.lean) | Formal-conjectures-shaped RHS with equivalence to `FC/Local.lean`. |
| [`docs/compact_cayley_proof.pdf`](docs/compact_cayley_proof.pdf) | Harjas / GPT-5.5 Pro, *A Fourier-Compactness Proof of Erdős Problem 42*, corrected version, 27 April 2026. |
| [`docs/combined_42_43_proof.pdf`](docs/combined_42_43_proof.pdf) | Kevin Barreto, *Sidon Difference Avoidance*, 29 April 2026 — combines #42 + #43. |
| [`docs/fourier_positive_ulam_note.pdf`](docs/fourier_positive_ulam_note.pdf) | natso26 / Tao, *A Fourier-positive proof of Erdős Problem 42*, draft note, 30 April 2026 — the cleanest exposition; we follow this layout. |
| [`docs/proof_outline.md`](docs/proof_outline.md) | Human-readable proof outline matching `fourier_positive_ulam_note.pdf`. |
| [`docs/forum.md`](docs/forum.md) | Snapshot of the forum thread (relevant comments + links). |
| [`safeverify/Spec.lean`](safeverify/Spec.lean) | SafeVerify target for Route A — public `Set ℕ` theorems (`theorem_1_1`, `erdos_42`) with `sorry` bodies. |
| [`safeverify/SpecCayley.lean`](safeverify/SpecCayley.lean) | SafeVerify target for Route B — flattened compact-Cayley major theorem surface, including `compact_cayley_clique` and `theorem_1_1_from_compact_cayley`, with `sorry` bodies. |

## How to verify

**Locally (with Lake):**
```
lake build Erdos.P42.Proof
lake build Erdos.P42.FourierPositive.Proof
lake build Erdos.P42.CompactCayley.Proof
```

**Online (single-file flat snapshots, Mathlib v4.28.0):**

- Route A (Fourier-positive, active):
  [live.lean-lang.org](https://live.lean-lang.org/#project=mathlib-v4.28.0&url=https%3A%2F%2Fraw.githubusercontent.com%2FShashi456%2Ferdos-formalizations%2Frefs%2Fheads%2Fmain%2FErdos%2FP42%2FFourierPositive%2FProof.lean)
- Route B (compact-Cayley, alternative; axiom-free):
  [live.lean-lang.org](https://live.lean-lang.org/#project=mathlib-v4.28.0&url=https%3A%2F%2Fraw.githubusercontent.com%2FShashi456%2Ferdos-formalizations%2Frefs%2Fheads%2Fmain%2FErdos%2FP42%2FCompactCayley%2FProof.lean)

## Current state

Route A is wired through the public FC-style statement. `lake build
Erdos.P42.Proof` builds the active umbrella without executable `sorry` warnings.
The public theorem depends on Mathlib foundations plus
`finite_fourier_avoidance_count`; it no longer depends on
`compact_cayley_clique`. The finite allowed/forbidden-difference Fourier
calculations and the elementary Sidon-size-over-prime smallness bound are proved.

| Theorem | Status |
|---|---|
| `compact_cayley_clique` | proved compact PDF Theorem 2.1 with a real normalized Fourier predicate; `#print axioms` reports only Mathlib foundations |
| `allowedDiffs_fourier_upper` | proved finite Fourier calculation for `T_A = ZMod p \ ((A - A) ∪ {0})` |
| `sidon_card_minus_one_div_prime_eventually_small` | proved elementary `|A| = O(sqrt N)` bound used to make `( |A|-1 ) / p ≤ ε` |
| `CompactCayley.cliqueKernelDensity_re_pos_iff_exists_clique` | proved finite endpoint: positive ordered `K_ℓ` Cayley density is equivalent to an actual `ℓ`-clique |
| `CompactCayley.cayleyConvolution`, `cayleyCutFunctional_eq_avg_convolution` | defined the finite convolution operator `Aψ(x)=E_y a(x-y)ψ(y)` and connected it to the cut functional |
| `CompactCayley.cayleyConvolution_stdAddChar` | proved the finite diagonalization identity: standard characters are eigenvectors of the Cayley convolution operator |
| `CompactCayley.cayleyConvolution_eq_fourier_sum` | proved arbitrary-test convolution diagonalization by Fourier expansion |
| `CompactCayley.cayleyCutFunctional_eq_fourier_sum` | proved algebraic core of compact-Cayley Lemma 2.5: the finite Cayley cut functional factors through normalized Fourier coefficients |
| `CompactCayley.sum_stdAddChar_mul_sub_eq_card_if` | proved finite character orthogonality needed for the Parseval step in Lemma 2.5 |
| `CompactCayley.cliqueEdgePairs_card_le_sq` | proved the elementary edge-count bound needed to control the finite telescoping sum |
| `CompactCayley.EdgeRest`, `CompactCayley.extendEdgeTuple`, `CompactCayley.edgeTupleEquiv`, `CompactCayley.sum_edgeTupleEquiv` | added the frozen-rest coordinate decomposition and finite-sum reindexing for isolating a single clique edge |
| `CompactCayley.edgeUsesVertex`, `CompactCayley.leftCliqueEdges`, `CompactCayley.rightCliqueEdges`, `CompactCayley.constantCliqueEdges` | partitioned the non-replaced clique edges by which endpoint variables they can depend on |
| `CompactCayley.remainingCliqueEdgeProduct_factorization` | proved the non-replaced edge product factors as a bounded left test times a bounded right test after freezing the remaining coordinates |
| `CompactCayley.edgeTuple_normalized_sum_eq_avgFinite_avgZMod` | proved the normalization bridge from the reindexed triple tuple sum to an average over two-variable normalized `ZMod p` averages |
| `CompactCayley.avg_mul_star_eq_sum_normalizedDftFunction` | proved Parseval cross identity in normalized-average form |
| `CompactCayley.sum_sq_norm_normalizedDftFunction_eq_avg` | proved normalized Parseval for arbitrary functions on `ZMod p` |
| `CompactCayley.norm_cayleyCutFunctional_le_spectral` | proved the finite spectral-cut core of compact-Cayley Lemma 2.5 for bounded test functions |
| `CompactCayley.SpectralBound`, `CompactCayley.CayleyCutBound`, `CompactCayley.cayleyCutBound_of_spectralBound` | packaged compact-Cayley Lemma 2.5 as a reusable spectral-bound-to-cut-bound implication for the later counting-convergence layer |
| `CompactCayley.finiteCliqueKernelDensity`, `CompactCayley.finiteCliqueKernelDensityEdge`, `CompactCayley.exists_clique_of_finiteCliqueKernelDensity_indicator_re_pos` | introduced the generic and edge-indexed finite `K_ℓ` density targets for compact-Cayley Lemma 2.6 and proved the indicator-positive endpoint gives a clique |
| `CompactCayley.replaceEdgeKernel`, `CompactCayley.finiteCliqueKernelWeightEdge_replace_sub`, `CompactCayley.finiteCliqueKernelDensityEdge_replace_sub` | proved the pointwise and normalized-density single-edge replacement identities used by the future telescoping proof of finite counting convergence |
| `CompactCayley.finiteCliqueKernelDensityEdge_replace_sub_reindex` | reindexed the single-edge density replacement sum by frozen-rest coordinates plus the two edge endpoints |
| `CompactCayley.norm_remainingCliqueEdgeProduct_le_one` | proved the bounded-test estimate for the product over all non-replaced clique edges |
| `CompactCayley.avgFinite`, `CompactCayley.norm_avgFinite_cayleyCutFunctional_le`, `CompactCayley.norm_finiteCliqueKernelDensityEdge_replace_sub_le_of_cut_representation` | added the finite averaging/cut-bound interface for the one-edge replacement estimate in Lemma 2.6 |
| `CompactCayley.finiteCliqueKernelDensityEdge_replace_sub_eq_avgFinite_cayleyCutFunctional_of_factorization`, `CompactCayley.norm_finiteCliqueKernelDensityEdge_replace_sub_le_of_factorization` | reduced the remaining one-edge replacement estimate to proving the non-replaced clique-edge product factors into bounded left/right tests |
| `CompactCayley.norm_finiteCliqueKernelDensityEdge_replace_sub_le_of_cutBound` | proved the concrete one-edge replacement estimate from the Cayley cut bound of the replaced-edge difference |
| `CompactCayley.patchEdgeKernel`, `CompactCayley.norm_finiteCliqueKernelDensityEdge_sub_le_card_mul_cutBound` | proved the finite telescoping estimate over all clique edges: edgewise Cayley cut bounds control the full finite `K_ℓ` density difference |
| `CompactCayley.norm_finiteCliqueKernelDensityEdge_sub_le_card_mul_spectralBound`, `CompactCayley.norm_finiteCliqueKernelDensity_sub_le_card_mul_spectralBound` | connected the all-edge telescoping estimate to the spectral hypothesis via Lemma 2.5's `cayleyCutBound_of_spectralBound` |
| `CompactCayley.exists_clique_of_spectral_density_transfer`, `CompactCayley.exists_clique_of_spectral_density_transfer_sq` | proved the finite endpoint that transfers positive model-kernel `K_ℓ` density plus spectral closeness to an actual clique in `T` |
| `CompactCayley.CayleyCounterSeq.finiteCliqueKernelDensity_indicatorC_eq_zero`, `finiteCliqueKernelDensity_indicatorC_tendsto_zero` | proved the B.6 finite contradiction consequence: a counterexample sequence has zero finite indicator clique density for every `n`, hence the densities tend to zero |
| `CompactCayley.theorem_1_1_from_compact_cayley` | preserved Route B downstream theorem over `Finset ℤ`, isolated in `CompactCayley/Main.lean` |
| `isSidonInt_of_isSidon` | proved bridge from bounded `Set ℕ` Sidon sets to `Finset ℤ` |
| `theorem_1_1` | proved public `Set ℕ` statement from Route A |
| `erdos_42` | proved FC-style wrapper under `answer := True` |
| `FormalConjecturesShape.erdos42RHS_iff_localRHS` | proved equivalence between the local wrapper RHS and the upstream-shaped RHS |
| `FormalConjecturesShape.erdos_42` | proved formal-conjectures-shaped theorem under `answer := True`, with FC's `∃ᵉ` represented by `ExplicitExists` |
| `FourierUpperIndicator` / `FourierLowerIndicator` | concrete normalized `ZMod.dft` predicates in `Shared/FiniteFourier.lean` |
| `normalizedDftFunction`, `function_eq_sum_normalizedDftFunction` | proved normalized arbitrary-function DFT API, the first shared finite-Fourier layer for opening both route axioms |
| `indicatorC_eq_sum_normalizedDftCoeff` | proved normalized finite Fourier inversion for indicator kernels |
| `CompactCayley.CompactCayleyCliqueStatementExplicit`, `compactCayleyCliqueStatement_from_explicit`, `explicit_of_compactCayleyCliqueStatement` | added the explicit-prime theorem shape and proved it equivalent to the original typeclass-shaped Route B statement |
| `CompactCayley.CayleyCounterSeq`, `CayleyCounterSeq.tendsto_p_atTop`, `CompactCayley.exists_cayleyCounterSeq_of_not_compactCayleyCliqueStatementExplicit` | formalized the Route B contradiction sequence for a failed compact-Cayley theorem, with primes `p_n > n`, `p_n → ∞`, density, zero-free symmetry, Fourier upper bias `ε_n → 0`, and no clique |
| `tao_continuous_avoidance` | proved continuous null-set endpoint, including the Haar shear/Fubini step |
| `continuousCliqueDensity_pos_of_pos_on_open_pi` | proved the open-box positivity criterion for continuous clique density |
| `continuousCliqueDensity_pos_of_pos_at_zero` | proved the `g(0) < 1` open-neighbourhood branch of compact-Cayley Lemma 2.7 after setting `f = 1 - g` |
| `continuousCliqueDensity_pos_of_one_sub_of_lt_one_at_zero` | proved the exact `g 0 < 1` formulation of compact-Cayley Lemma 2.7's first branch |
| `continuousCliqueDensity_pos_of_zeroLevel_proper_subgroup` | proved compact-forcing endpoint: a kernel vanishing exactly on a proper closed subgroup has positive continuous `K_M` density |
| `continuousCliqueDensity_pos_of_one_sub_level_one_proper_subgroup` | proved the Route B Lemma 2.7 measure-theoretic corollary for the `g = 1 - f` formulation; the remaining Lemma 2.7 gap is the positive-definite proof that `{x | g x = 1}` is a proper closed subgroup |
| `continuousWeightedAvoidanceKernel`, `continuousWeightedAvoidanceDensity`, `continuousWeightedAvoidanceDensity_pos_of_level_one_proper_subgroup`, `continuousWeightedAvoidanceDensity_pos_of_level_one_proper_subgroup_of_integral_ge` | added the Route A weighted continuous endpoint: once `{x | f x = 1}` is a proper closed subgroup and the compact-model vertex weight satisfies `α ≤ ∫ u` with `α > 0`, the weighted avoidance integral is strictly positive |
| `LevelOneSubgroupKernel`, `levelOneAddSubgroup`, `continuousCliqueDensity_pos_of_levelOneSubgroupKernel` | proved the subgroup/properness wrapper for Lemma 2.7: once positive-definiteness gives level-one closure, the continuous clique-forcing density conclusion follows |
| `closed_subgroup_haar_null_of_not_finiteIndex` | isolated the finite-index half of the Haar-null argument: any closed subgroup with nonzero Haar measure has finite index, giving a nullness route for extraction-dual subgroups without first proving full connectedness |
| `continuousWeightedAvoidanceDensity_pos_of_level_one_null_subgroup`, `continuousWeightedAvoidanceDensity_pos_of_level_one_null_subgroup_of_integral_ge`, `continuousWeightedAvoidanceDensity_pos_of_levelOneSubgroupKernel` | added the Route A weighted endpoint in two forms: a sharper null-subgroup endpoint that avoids connectedness, and the connected/proper subgroup wrapper used by the original compact-model interface |
| `RealHilbertKernelRepresentation`, `levelOneSubgroupKernel_of_realHilbertKernelRepresentation` | proved that a unit-vector Hilbert representation of the positive-definite kernel gives the level-one closure property |
| `continuousCliqueDensity_pos_of_realHilbertKernelRepresentation` | proved the Hilbert-representation form of Lemma 2.7's endpoint, reducing the remaining positive-definite work to constructing the unit-vector representation |
| `continuousCliqueDensity_pos_of_lt_one_or_levelOneSubgroupKernel`, `continuousCliqueDensity_pos_of_lt_one_or_realHilbertKernelRepresentation` | packaged Lemma 2.7's two branches into endpoint theorems; the remaining gap is now producing the level-one/Hilbert representation from Fourier positivity in the `g 0 = 1` branch |
| `FourierPositive.finite_fourier_avoidance_count` | theorem-shaped Route A axiom, matching the count form of the Green-Tao/Fourier-positive finite avoidance theorem |
| `FourierPositive.finite_fourier_avoidance_exists` | derived theorem from the count axiom; this is the interface used downstream |
| `FourierPositive.FiniteFourierAvoidanceCountStatementExplicit`, `explicit_of_finite_fourier_avoidance_count_statement`, `finite_fourier_avoidance_count_statement_from_explicit` | added the explicit-prime theorem shape for Route A and proved it equivalent to the original typeclass-shaped count statement |
| `FourierPositive.FourierAvoidanceCounterSeq`, `FourierAvoidanceCounterSeq.tendsto_p_atTop`, `exists_fourierAvoidanceCounterSeq_of_not_finiteFourierAvoidanceCountStatementExplicit` | formalized the Route A contradiction sequence for a failed finite Fourier avoidance count theorem, with primes `p_n ≥ n`, `p_n → ∞`, dense `U_n`, symmetric forbidden `F_n`, Fourier lower bias `ε_n → 0`, and tuple counts below `c_n p_n^m` |
| `FourierPositive.pairEdgePairs`, `finiteWeightedPattern`, `finiteAvoidanceDensity`, `finiteAvoidanceDensity_inclusion_exclusion` | introduced the Route A weighted pattern-count layer and proved the finite inclusion-exclusion identity that expands avoidance density into complexity-one edge-pattern counts |
| `FourierPositive.finiteWeightedPatternEdge`, `finiteWeightedPatternEdge_replace_sub`, `patchPairEdgeKernel`, `norm_finiteWeightedPatternEdge_patch_sub_le_card_mul`, `norm_finiteWeightedPatternEdge_sub_le_card_mul` | added the Route A one-edge replacement and finite telescoping algebra for weighted pattern counts; this is the finite backbone of the future weighted counting-convergence proof |
| `FourierPositive.weightedCayleyCutFunctional`, `WeightedCayleyCutBound`, `norm_finiteWeightedPatternEdge_replace_sub_le_of_cut_representation` | added the Route A cut-bound interface: a factored one-edge replacement average of bounded Cayley cut functionals gives the required one-edge norm bound |
| `FourierPositive.PairEdgeRestAssignment`, `pairEdgeTupleEquiv`, `pairEdgeTuple_normalized_sum_eq_avgFinite_avgZMod`, `finiteWeightedPatternEdge_replace_sub_reindex`, `finiteWeightedPatternEdge_replace_sub_eq_avgFinite_weightedCayleyCutFunctional_of_factorization` | added the Route A frozen-coordinate reindexing and generic factorization theorem turning a one-edge replacement into an average of weighted Cayley cut functionals |
| `FourierPositive.remainingPairEdgeProduct_factorization`, `vertexProduct_factorization`, `weightedPairRemainingProduct_factorization`, `finiteWeightedPatternEdge_replace_sub_eq_avgFinite_weightedCayleyCutFunctional` | proved the concrete frozen-coordinate factorization for Route A: after one edge is replaced, all other edge and vertex weights split into bounded left/right tests for the weighted Cayley cut functional |
| `FourierPositive.PairKernelBoundedByOne`, `VertexWeightBoundedByOne`, `norm_weightedLeftPairTest_le_one`, `norm_weightedRightPairTest_le_one`, `norm_finiteWeightedPatternEdge_replace_sub_le_of_cutBound` | proved the concrete one-edge replacement estimate for Route A: bounded weighted patterns are controlled by the weighted Cayley cut bound of the replaced-edge difference |
| `FourierPositive.PairKernelBoundedByOne.patch`, `norm_finiteWeightedPatternEdge_patch_insert_sub_le_of_cutBound`, `norm_finiteWeightedPatternEdge_sub_le_card_mul_cutBound` | upgraded the Route A telescoping lemma to a concrete all-edge estimate: edgewise weighted Cayley cut bounds control the full weighted pattern-count difference by `|E| * M` |
| `FourierPositive.weightedCayleyCutFunctional_eq_fourier_sum`, `sum_sq_norm_normalizedDftFunction_eq_avg`, `weightedCayleyCutBound_of_spectralBound` | added the Route A finite spectral-cut theorem: normalized Fourier coefficient bounds imply weighted Cayley cut bounds for all bounded tests |
| `FourierPositive.avgConvolution`, `normalizedDftFunction_avgConvolution`, `norm_avgConvolution_indicator_le_of_kernel_real_nonneg_avg_one` | added normalized finite convolution on `ZMod p`, proved that the normalized DFT turns convolution into pointwise multiplication, and proved the finite positivity bound that `1_F * K` stays uniformly bounded when `K` is real nonnegative with average `1` |
| `FourierPositive.largeSpectrum`, `largeSpectrum_mono`, `largeSpectrum_card_le_inv_sq_of_norm_le_one`, `largeSpectrum_indicatorC_card_le_pow_two_sq`, `FourierAvoidanceCounterSeq.largeSpectrumAt`, `largeSpectrumAt_mono`, `largeSpectrumLabelBound`, `largeSpectrumAtEmbedding`, `largeSpectrumLabelFreq`, `largeSpectrumLabelFreq_embedding` | added the Route A large-spectrum Parseval bound and sequence-level labelling API: bounded functions have uniformly finite nested dyadic large spectra, every counterexample large spectrum embeds into the fixed finite label type `Fin ⌈(2^k)^2⌉₊`, and each used label recovers its represented frequency |
| `FourierPositive.real_limit_nonneg_of_eventually_lower_neg_tendsto_zero`, `complex_limit_re_nonneg_and_im_zero`, `FourierAvoidanceCounterSeq.fourierCoeff_limit_re_nonneg_and_im_zero`, `forbiddenCoeff_subseq_limit_re_nonneg_and_im_zero`, `zero_forbiddenCoeff_subseq_limit_le_one_sub_rho_and_im_zero`, `zero_vertexCoeff_subseq_limit_ge_alpha_and_im_zero`, `exists_strictMono_subseq_tendsto_countable_family_of_norm_le_one`, `exists_forbidden_and_vertexCoeff_subseq_tendsto_countable` | added the Route A Fourier-coefficient limit consequences and compactness extraction tools: convergent forbidden-set coefficients have real nonnegative limits, zero coefficients give the future mean bounds, subsequence limits preserve these facts, and every finite or countable family of bounded forbidden/vertex coefficient sequences has a common strictly monotone convergent subsequence |
| `FourierPositive.exists_strictMono_subseq_eventually_const_countable_family` | added countable diagonal stabilization for decidable relation predicates, needed so formal quotient relations can be made eventually stable before proving finite-lift average convergence |
| `FourierPositive.CountableCoeffLimitData`, `exists_countableCoeffLimitData`, `CountableCoeffLimitData.fCoeff_zero_index_le_one_sub_rho_and_im_zero`, `uCoeff_zero_index_ge_alpha_and_im_zero` | packaged countable diagonal extraction into named limit coefficient functions along one subsequence, including real nonnegative forbidden limits and zero-index mean-bound accessors |
| `FourierPositive.LargeSpectrumIndex`, `FourierAvoidanceCounterSeq.largeSpectrumIndexFreq`, `exists_largeSpectrumIndexFreq_eq_of_mem`, `LargeSpectrumCoeffLimitData`, `exists_largeSpectrumCoeffLimitData` | specialized the countable coefficient-limit package to the actual labelled dyadic large spectra, giving one subsequence and named forbidden/vertex limits for every large-spectrum label |
| `FourierPositive.ExtendedLargeSpectrumIndex`, `FourierAvoidanceCounterSeq.extendedLargeSpectrumIndexFreq`, `ExtendedLargeSpectrumCoeffLimitData`, `exists_extendedLargeSpectrumCoeffLimitData` | extended the labelled large-spectrum coefficient package with an explicit zero-character index, so the extracted coefficient data carries both large-spectrum limits and the zero-frequency mean bounds needed by the compact model |
| `FourierPositive.StableExtendedLargeSpectrumCoeffLimitData`, `exists_stableExtendedLargeSpectrumCoeffLimitData`, `StableExtendedLargeSpectrumCoeffLimitData.subseq`, `StableExtractionCoeffLimitData`, `StableExtendedLargeSpectrumCoeffLimitData.exists_stableExtractionCoeffLimitData`, `FourierAvoidanceCounterSeq.exists_stableExtractionCoeffLimitData` | refined the extended large-spectrum extraction to a relation-stable subsequence, proved relation-stability survives further subsequences, and added the diagonal coefficient package for all formal free-group frequencies used by fixed Fejer/trigonometric-polynomial counts |
| `FourierPositive.ExtractionFreeGroup`, `extractionFiniteLiftHom`, `extractionEventualKernel`, `ExtractionDiscreteGroup`, `extractionDiscreteGroup_isAddTorsionFree` | began the Route A compact-dual algebraic skeleton: free abelian group on extended labels, finite lift homomorphisms, eventual-kernel quotient, quotient/frequency equality API, and the torsion-free proof needed for the future connected dual |
| `FourierPositive.ExtractionDualDomain`, `ExtractionCompactDual`, `ExtractionCompactAddDual`, `extractionCompactDual_compactSpace`, `extractionCompactDual_isTopologicalGroup`, `extractionCompactAddDualSecondCountableTopology`, `extractionCompactAddDualHaar` | installed the discrete topology/countability on the extraction quotient, defined the Pontryagin compact dual and additive wrapper, proved second-countability and measurable group operations, and normalized the whole compact group to an additive Haar probability measure for the future Route A compact model |
| `FourierPositive.ExtractionTrigPoly`, `ExtractionTrigPoly.eval`, `ExtractionTrigPoly.continuous_eval`, `ExtractionTrigPoly.evalFinite`, `ExtractionTrigPoly.finiteAverage`, `ExtractionTrigPoly.compactAverage`, `avgZMod_stdAddChar_neg_mul_eq_ite`, `extractionCharacterValue_add`, `norm_extractionCharacterValue`, `StableExtractionCoeffLimitData.fCoeffQ`, `StableExtractionCoeffLimitData.uCoeffQ`, `StableExtractionCoeffLimitData.fCoeffQ_tendsto`, `StableExtractionCoeffLimitData.uCoeffQ_tendsto`, `ExtractionTrigPoly.forbiddenWeightedFiniteAverage`, `ExtractionTrigPoly.vertexWeightedFiniteAverage`, `StableExtractionCoeffLimitData.forbiddenWeightedFiniteAverage_tendsto_coeffFunctional`, `StableExtractionCoeffLimitData.vertexWeightedFiniteAverage_tendsto_coeffFunctional`, `extractionFiniteLiftFreq_generator_eventually_eq`, `extractionLargeSpectrumGeneratorFinset`, `extractionLargeSpectrumGeneratorFinset_eventually_represents_largeSpectrumAt`, `extractionFiniteLiftFreq_sub_eventually_eq`, `extractionFiniteLiftFreq_neg_eventually_eq`, `StableExtendedLargeSpectrumCoeffLimitData.extractionFiniteLiftFreq_eventually_injOn_finset`, `StableExtendedLargeSpectrumCoeffLimitData.finiteAverage_eventually_eq_zeroCoeff`, `StableExtendedLargeSpectrumCoeffLimitData.finiteAverage_tendsto_compactAverage` | added the Route A trigonometric-polynomial skeleton on the extraction quotient, including compact-dual character algebra/norm facts, compact-side evaluation/additivity/continuity, finite cyclic evaluation, finite averages, quotient-facing coefficient limits, weighted finite averages against `1_F` and `1_U`, convergence of fixed lifted trig-polynomial weighted averages to the extracted coefficient functionals, the `if r = 0 then 1 else 0` finite character-average wrapper, eventual finite-lift subtraction/negation and finite-set injectivity, an abstract compact-average/zero-frequency interface, zero/nonzero single-character average lemmas, eventual recovery of generator-labelled finite frequencies, a finset bridge from each finite dyadic large spectrum to extracted generators, and compact-average convergence for relation-stable lifted trigonometric polynomials |
| `FourierPositive.extractionAddCharacterValue`, `ExtractionTrigPoly.evalAdd`, `ExtractionTrigPoly.continuous_evalAdd`, `extractionCompactAddFejerKernel`, `extractionFejerTrigPoly_evalAdd`, `extractionCompactAddFejerKernel_continuous`, `extractionCompactAddFejerKernel_re_nonneg` | added additive compact-dual wrappers for Route A trigonometric polynomials and Fejer kernels, so the smoothing kernels can be used directly on the additive Haar compact group required by `WeightedCompactModel` |
| `FourierPositive.extractionCompactFejerKernel`, `extractionFiniteFejerKernel`, `extractionFiniteFejerKernelAverage`, `extractionFiniteSmoothedForbiddenKernel`, `normalizedDftFunction_extractionFiniteSmoothedForbiddenKernel`, `StableExtractionCoeffLimitData.normalizedDftFunction_extractionFiniteFejerKernel_at_pos_lift_eventually_eq_coeff`, `StableExtractionCoeffLimitData.normalizedDftFunction_extractionFiniteSmoothedForbiddenKernel_at_lift_tendsto`, `StableExtractionCoeffLimitData.compactSmoothedForbiddenTrigPoly`, `StableExtractionCoeffLimitData.compactSmoothedForbiddenTrigPoly_apply`, `StableExtractionCoeffLimitData.normalizedDftFunction_extractionFiniteSmoothedForbiddenKernel_at_neg_lift_tendsto_compactCoeff`, `extractionFiniteSmoothedForbiddenWeightedAverage`, `StableExtractionCoeffLimitData.smoothedForbiddenCoeffFunctional`, `StableExtractionCoeffLimitData.extractionFiniteSmoothedForbiddenWeightedAverage_tendsto_coeffFunctional`, `norm_normalizedDftFunction_extractionFiniteSmoothedForbiddenKernel_le_fejer`, `normalizedDftFunction_indicator_sub_extractionFiniteSmoothedForbiddenKernel`, `norm_normalizedDftFunction_indicator_sub_extractionFiniteSmoothedForbiddenKernel_le`, `weightedSpectralBound_extractionFiniteSmoothedForbiddenKernel_sub_indicatorC`, `norm_finiteKernelAvoidanceDensity_extractionFiniteSmoothedForbiddenKernel_sub_finiteAvoidanceDensity_le`, `extractionFiniteSmoothedForbiddenKernel_norm_le_one_of_average_eq_one`, `StableExtendedLargeSpectrumCoeffLimitData.extractionFiniteSmoothedForbiddenKernel_norm_le_one_eventually`, `extractionFejerTrigPoly`, `extractionFejerTrigPoly_eval`, `extractionFejerTrigPoly_apply_sum`, `extractionFejerTrigPoly_apply_filter_card`, `ExtractionFejerCoeffBound`, `ExtractionFejerPairCoeffBound`, `ExtractionFejerPairCoeffRealBound`, `extractionFejerCoeffBound_of_pairCoeffRealBound`, `extractionFejerPairFilter_card_le`, `StableExtendedLargeSpectrumCoeffLimitData.norm_one_sub_normalizedDftFunction_extractionFiniteFejerKernel_at_lift_eventually_le_on_finset`, `extractionFejerTrigPoly_compactAverage_eq_one_of_nonempty`, `StableExtendedLargeSpectrumCoeffLimitData.extractionFejerTrigPoly_evalFinite_eventually_eq`, `StableExtendedLargeSpectrumCoeffLimitData.normalizedDftFunction_extractionFiniteFejerKernel_eventually_eq`, `StableExtendedLargeSpectrumCoeffLimitData.normalizedDftFunction_extractionFiniteFejerKernel_at_lift_eventually_eq_coeff`, `StableExtendedLargeSpectrumCoeffLimitData.norm_one_sub_normalizedDftFunction_extractionFiniteFejerKernel_at_lift_eventually_le`, `StableExtendedLargeSpectrumCoeffLimitData.norm_one_sub_normalizedDftFunction_extractionFiniteFejerKernel_at_pos_lift_eventually_le`, `StableExtendedLargeSpectrumCoeffLimitData.extractionFiniteFejerKernelAverage_tendsto_compactAverage`, `StableExtendedLargeSpectrumCoeffLimitData.extractionFiniteFejerKernelAverage_eventually_eq_one`, `extractionCompactFejerKernel_continuous`, `extractionCompactFejerKernel_re_nonneg`, `extractionCompactFejerKernel_im_eq_zero`, `extractionFiniteFejerKernel_re_nonneg`, `extractionFiniteFejerKernel_im_eq_zero` | introduced the Route A Fejer smoothing kernels on the extraction compact dual and finite cyclic lifts, represented the compact kernel by an extraction trigonometric polynomial, proved the compact coefficient equals the normalized count of difference pairs, added complex and real pair-count Fejer coefficient-bound interfaces, proved the fixed-difference pair fiber has cardinality at most `|Q|`, proved the relation-stable finite lift eventually equals the finite cyclic kernel, proved the finite DFT formula for lifted Fejer kernels and its negative/positive represented-frequency coefficient specializations, proved the DFT coefficient of the Fejer-smoothed forbidden kernel at each fixed extracted frequency converges to the expected forbidden-limit times compact-Fejer coefficient product, packaged those limits as a finite-support compact smoothed forbidden trigonometric polynomial, proved convergence of finite averages of the smoothed forbidden kernel against any fixed lifted trigonometric polynomial, proved compact/finite average normalization for nonempty frequency sets, kept compact/finite kernels real and pointwise nonnegative, named the finite smoothed forbidden kernel with its Fourier product formula, proved the smoothed kernel is eventually bounded by `1`, and connected its spectral Fejer error to the full finite weighted avoidance-density replacement bound |
| `FourierPositive.norm_normalizedDftFunction_le_norm_average`, `norm_normalizedDftFunction_le_one_of_kernel_real_nonneg_avg_one`, `ExtractionFejerNegCoeffBound`, `extractionFejerNegCoeffBound_of_pairCoeffRealBound_neg`, `StableExtendedLargeSpectrumCoeffLimitData.norm_one_sub_normalizedDftFunction_extractionFiniteFejerKernel_at_pos_lift_eventually_le_on_finset`, `StableExtendedLargeSpectrumCoeffLimitData.norm_one_sub_normalizedDftFunction_extractionFiniteFejerKernel_on_largeSpectrumAt_eventually_le`, `norm_one_sub_normalizedDftFunction_extractionFiniteFejerKernel_le_two_of_average_eq_one`, `norm_normalizedDftFunction_indicator_sub_extractionFiniteSmoothedForbiddenKernel_le_of_notMem_largeSpectrumAt`, `StableExtendedLargeSpectrumCoeffLimitData.norm_normalizedDftFunction_indicator_sub_extractionFiniteSmoothedForbiddenKernel_on_largeSpectrumAt_eventually_le`, `StableExtendedLargeSpectrumCoeffLimitData.weightedSpectralBound_extractionFiniteSmoothedForbiddenKernel_sub_indicatorC_eventually`, `StableExtendedLargeSpectrumCoeffLimitData.norm_finiteKernelAvoidanceDensity_extractionFiniteSmoothedForbiddenKernel_sub_finiteAvoidanceDensity_eventually_le`, `StableExtendedLargeSpectrumCoeffLimitData.norm_finiteKernelAvoidanceDensity_extractionFiniteSmoothedForbiddenKernel_sub_finiteAvoidanceDensity_eventually_le_of_pairCoeffRealBound_neg` | completed the finite high/low-spectrum Fejer smoothing bridge: real nonnegative average-one kernels have normalized Fourier coefficients of norm at most `1`; high-spectrum frequencies are controlled by extracted generator coefficients; low-spectrum frequencies cost at most `2 * 2^{-k}`; and the combined estimate gives the finite weighted avoidance-density error bound needed for Route A counting convergence directly from the real pair-overlap condition expected from Følner boxes |
| `FourierPositive.norm_finiteWeightedPatternEdge_sub_le_card_mul_spectralBound`, `norm_finiteWeightedPattern_sub_le_card_mul_spectralBound` | connected Route A finite weighted pattern-count telescoping directly to edgewise/common-kernel spectral bounds |
| `FourierPositive.indicatorC_norm_le_one`, `vertexWeightBoundedByOne_indicatorC`, `norm_finiteWeightedPattern_sub_indicator_le_card_mul_spectralBound` | specialized the Route A spectral counting estimate to the actual `1_F` forbidden kernel and `1_U` vertex weight used by finite avoidance |
| `FourierPositive.finiteKernelAvoidanceDensity`, `finiteKernelAvoidanceDensity_inclusion_exclusion`, `norm_finiteKernelAvoidanceDensity_sub_finiteAvoidanceDensity_le_spectral` | added the generic smoothed-kernel avoidance density and proved spectral closeness to `1_F` controls the full finite avoidance density by summing the weighted pattern errors over all edge subsets |
| `FourierPositive.sum_powerset_card_mul_le_card_mul_two_pow`, `norm_finiteKernelAvoidanceDensity_sub_finiteAvoidanceDensity_le_spectral_closed` | packaged the full finite avoidance-density error into the coarse closed-form bound `|K_m| * 2^|K_m| * M`, useful for later small-error choices |
| `FourierPositive.AvoidsForbiddenDiffsOriented`, `avoidsForbiddenDiffs_iff_oriented_of_symmetric`, `finiteAvoidanceWeight_eq_indicator_oriented`, `finiteAvoidanceDensity_eq_oriented_count` | connected the normalized weighted avoidance density to the actual oriented avoiding-tuple count, with equivalence to the all-ordered-pairs predicate for symmetric forbidden sets |
| `FourierPositive.finiteAvoidingTupleFinset`, `finiteAvoidingTupleFinset_eq_oriented_of_symmetric`, `finiteAvoidanceDensity_eq_count_of_symmetric` | matched the Route A normalized avoidance density to the exact avoiding-tuple finset used by `finite_fourier_avoidance_count` whenever `F` is symmetric |
| `FourierPositive.normalizedAvoidanceDensity`, `finiteAvoidanceDensity_eq_normalizedAvoidanceDensity_of_symmetric`, `FourierAvoidanceCounterSeq.normalizedAvoidanceDensity_tendsto_zero`, `FourierAvoidanceCounterSeq.finiteAvoidanceDensity_tendsto_zero`, `FourierAvoidanceCounterSeq.finiteAvoidanceDensity_re_tendsto_zero` | added the real and complex normalized avoidance densities and proved every Route A counterexample sequence has `Λ_n → 0`, including the real-part form needed by the future compact integral limit |
| `FourierPositive.WeightedCompactModel`, `FourierPositive.WeightedCompactNullModel`, `FourierPositive.WeightedCompactInfiniteIndexModel`, `WeightedCompactInfiniteIndexModel.toNullModel`, `HasExtractionWeightedCompactNullModel`, `HasExtractionWeightedCompactInfiniteIndexModel`, `hasWeightedCompactNullModel_of_hasExtractionWeightedCompactNullModel`, `hasWeightedCompactNullModel_of_hasExtractionWeightedCompactInfiniteIndexModel`, `finite_fourier_avoidance_count_statement_of_forall_hasExtractionWeightedCompactNullModel`, `finite_fourier_avoidance_count_statement_of_forall_hasExtractionWeightedCompactInfiniteIndexModel`, `FourierAvoidanceCounterSeq.false_of_weightedCompactModel`, `FourierAvoidanceCounterSeq.false_of_weightedCompactNullModel`, `FourierAvoidanceCounterSeq.false_of_weightedCompactInfiniteIndexModel`, `not_exists_counterSeq_with_weightedCompactModel`, `not_exists_counterSeq_with_weightedCompactNullModel` | packaged the Route A compact-model contradiction in connected/proper-subgroup, sharper null-subgroup, infinite-index subgroup, and concrete extraction-dual forms: any counterexample sequence with one of these compact models and counting convergence is impossible, so the remaining Route A gap is isolated to constructing the extraction-dual model and proving the level-one subgroup is null/infinite-index |
| `FourierPositive.forbiddenDiffSetMod_symmetric`, `zero_mem_forbiddenDiffSetMod`, `forbiddenDiffSetMod_card_le` | proved finite forbidden-set setup for `F_A = A - A mod p` |
| `FourierPositive.sidon_forbidden_fourier_lower` | proved normalized Fourier lower bound for `F_A`; axiom audit reports only Mathlib foundations |
| `FourierPositive.theorem_1_1_from_finite_fourier_avoidance` | proved downstream over `Finset ℤ` from the derived existence theorem and greedy Sidon extraction |

Route A builds with:

```
lake build Erdos.P42.FourierPositive.Proof
lake build Erdos.P42.FourierPositive.Main
```

The active modular umbrella `Erdos.P42.Proof` imports `FC/Shape.lean` directly rather
than importing the flat file, so the full project can still import modular P42
files without duplicate declarations. Route B builds separately with:

```
lake build Erdos.P42.CompactCayley.Proof
```

## Target trust boundary

Beyond Mathlib core (`propext`, `Classical.choice`, `Quot.sound`):

| Theorem | Extra axioms (target) |
|---|---|
| `theorem_1_1`, `erdos_42` via Route A | `finite_fourier_avoidance_count` |
| `CompactCayley.compact_cayley_clique`, `CompactCayley.theorem_1_1_from_compact_cayley` | none beyond Mathlib foundations |
| Route A finite setup lemmas | none beyond Mathlib foundations |
| Route B finite setup lemmas | none beyond Mathlib foundations |

`#print axioms Erdos42.theorem_1_1` and `#print axioms Erdos42.erdos_42`
currently report Mathlib foundations plus `finite_fourier_avoidance_count`.
The internal finite endpoint
`Erdos42.CompactCayley.cliqueKernelDensity_re_pos_iff_exists_clique` reports
only Mathlib foundations. `#print axioms
Erdos42.CompactCayley.compact_cayley_clique` and `#print axioms
Erdos42.CompactCayley.theorem_1_1_from_compact_cayley` also report only Mathlib
foundations. The continuous endpoints
`Erdos42.tao_continuous_avoidance` and
`Erdos42.continuousCliqueDensity_pos_of_zeroLevel_proper_subgroup` also report
only Mathlib foundations. For Route A, the finite forbidden-set lemmas through
`Erdos42.FourierPositive.sidon_forbidden_fourier_lower` also report only Mathlib
foundations.

## Verifying with SafeVerify

[SafeVerify](https://github.com/GasStationManager/SafeVerify) replays each
declaration through the kernel via `Environment.replay`, enforces a hard
axiom allow-list, and bans `partial` / `unsafe` constants. Both routes have
their own spec, and both pass replay against the corresponding submission
`.olean`.

The required allow-list starts with Mathlib core (`propext`, `Quot.sound`,
`Classical.choice`). Route A still has one local trust-boundary axiom; Route B
now uses Mathlib core only.

| Route | Spec | Submission `.olean` | Extra allowed axiom |
|---|---|---|---|
| A (Fourier-positive, active) | `safeverify/Spec.lean` | `Erdos.P42.Proof` | `Erdos42.FourierPositive.finite_fourier_avoidance_count` |
| B (compact-Cayley) | `safeverify/SpecCayley.lean` | `Erdos.P42.CompactCayley.Proof` | none |

Reproduction, from a checkout of this repo at the same parent directory as
SafeVerify (with `lake exe safe_verify` available):

```
# Build everything in this repo first.
lake build Erdos.P42.Proof Erdos.P42.CompactCayley.Proof

# Build the two spec oleans.
lake env lean -o Erdos/P42/safeverify/Spec.olean Erdos/P42/safeverify/Spec.lean
lake env lean -o Erdos/P42/safeverify/SpecCayley.olean Erdos/P42/safeverify/SpecCayley.lean

# Run SafeVerify (LEAN_PATH must include this repo's .lake build dir).
cd ../SafeVerify
LEAN_PATH="../erdos-formalizations/.lake/build/lib/lean:$(lake env printenv LEAN_PATH)" \
  lake exe safe_verify --disallow-partial \
    ../erdos-formalizations/Erdos/P42/safeverify/Spec.olean \
    ../erdos-formalizations/.lake/build/lib/lean/Erdos/P42/Proof.olean

LEAN_PATH="../erdos-formalizations/.lake/build/lib/lean:$(lake env printenv LEAN_PATH)" \
  lake exe safe_verify --disallow-partial \
    ../erdos-formalizations/Erdos/P42/safeverify/SpecCayley.olean \
    ../erdos-formalizations/.lake/build/lib/lean/Erdos/P42/CompactCayley/Proof.olean
```

Both runs end with `SafeVerify check passed.` — Route A matches 4
declarations (`IsSidon`, `IsMaximalSidonSetIn`, `theorem_1_1`, `erdos_42`),
Route B matches 49 spec declarations, including the compact-Cayley theorem
shape, countersequence contradiction, finite spectral/counting endpoint,
`compact_cayley_clique`, and `theorem_1_1_from_compact_cayley`. Route B no
longer needs a local trust-boundary axiom.

## Comparison with Sedov's `M = 3` formalization

Daniil Sedov's [github.com/Gusarich/erdos42](https://github.com/Gusarich/erdos42) handles the **special case `M = 3`** via a sum-free 2/5-trichotomy axiom (Balogh-Liu-Sharifzadeh-Treglown, 2014). Our target is the **general `M`** case via the Fourier-compactness route.

The two approaches are independent — Sedov's axiom is a finite Ramsey/sum-free statement; ours is Green-Tao analytic. There's no direct sharing of code or lemmas, but Sedov's `IsSidon` API and `(A − A) ∩ (B − B) ⊆ {0}` lemmas may be re-usable.

## Alignment with the informal proof

[`docs/fourier_positive_ulam_note.pdf`](docs/fourier_positive_ulam_note.pdf) is the canonical reference for
Route A; we audit `FourierPositive/Proof.lean` and `FourierPositive/Main.lean`
against it section-by-section. The compact-Cayley PDF is tracked by the modular
`CompactCayley` files, with `CompactCayley/Proof.lean` as the buildable flat
audit artifact.

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
