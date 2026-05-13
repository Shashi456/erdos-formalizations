/-
Erdős Problem 202 — compressed proof.

This file restates `erdos202_main` along with the full named trust boundary
(8 named axioms + Lean foundations). It is the single-file "proof certificate"
view of the formalization: a reader who trusts the listed axioms gets the
sharp BFV asymptotic

    f(N) = N · exp(-(1 + o(1)) · sqrt(log N · log log N))

as a Lean theorem.

# Structure

§1.  Imports & the main theorem (proved, no `sorry`).
§2.  Statement-layer recap.
§3.  Trust boundary — every axiom transitively used by `erdos202_main`.
§4.  Axiom audit (commented `#print axioms` outputs).
-/

import Mathlib
import Erdos.P202.P202Main
import Erdos.P202.ParkPham.SpreadDisjointness
import Erdos.P202.BFV.LowerBoundInput
import Erdos.P202.BFV.Pruning
import Erdos.P202.BFV.LowerConstruction
import Erdos.P202.BFV.Mertens
import Erdos.P202.BFV.Chebyshev
import Erdos.P202.BFV.HExpRare
import Erdos.P202.BFV.RadMultiplicity

namespace Erdos202.Compressed

open Filter

/-! ## §1 Main theorem

The sharp asymptotic for the Erdős 202 extremal function `f`, packaged
as a single theorem with no `sorry`s — every leaf is either a Lean
foundational axiom (`propext`, `Classical.choice`, `Quot.sound`) or one
of the named project-level axioms listed in §3 below. -/

/-- **Erdős Problem 202 (sharp BFV asymptotic).** For every `ε > 0`,
eventually in `N`,

  `N · L(-(1+ε), N) ≤ f(N) ≤ N · L(-(1-ε), N)`

where `L(α, N) = exp(α · sqrt(log N · log log N))`.

Equivalently: `f(N) = N · exp(-(1 + o(1)) · sqrt(log N · log log N))`.

Proved against the trust boundary in §3. -/
theorem erdos202_sharp_asymptotic : Erdos202.Erdos202Statement :=
  Erdos202.erdos202_main

/-! ## §2 Statement-layer recap

`f(N)` is the extremal function for the Erdős 202 problem (maximum size
of an admissible family of residue classes covering at most `N` integers
— see `P202Basic.lean`).

`Lscale α N := exp(α · sqrt(log N · log log N))` is the BFV scale.

`HasErdos202Asymptotic F` is the two-sided epsilon-form of
`F N = N · L(-(1 + o(1)), N)`.

`Erdos202Statement := HasErdos202Asymptotic f`. -/

/-! ## §3 Trust boundary

`erdos202_main` reduces to the following named axioms (transitively).
Each axiom has a docstring in its file with the classical statement and
references; the named-stub discipline ensures each axiom is a single
clean analytic or finite-combinatorial primitive that could plausibly
be discharged in a focused subproject. -/

section TrustBoundary

/-! ### §3.1 Park–Pham layer

The deep gap: the Kahn–Kalai expectation-threshold conjecture, proved by
Jinyoung Park and Huy Tuan Pham in 2022 (arXiv:2203.17207). All upper-
bound consequences of the spread-disjointness chain reduce to this. -/

/-- Park–Pham/Kahn–Kalai absolute constant `C_KK`.
File: `Erdos/P202/ParkPham/Threshold.lean`. -/
noncomputable example : ℝ := Erdos202.ParkPham.CKK_const

/-- Positivity of `C_KK`. -/
example : 0 < Erdos202.ParkPham.CKK_const := Erdos202.ParkPham.CKK_const_pos

/-- The Park–Pham expectation-threshold theorem in finite form: at any
density `p ≥ C_KK · q · log(ℓ(U))`, the Bernoulli product measure of an
increasing family `U` is at least `1/2`. -/
example := @Erdos202.ParkPham.park_pham_threshold

/-- Random-partition double-counting: lifts `muP ≥ 1/2` at density
`1/(2r)` to the existence of `r` pairwise-disjoint members of `A`.
Finite combinatorics, no analytic content.
File: `Erdos/P202/ParkPham/SpreadDisjointness.lean`. -/
example := @Erdos202.ParkPham.partition_density_to_disjoint_members

/-! ### §3.2 BFV layer — analytic primitives

These are Mathlib-PR-style targets: classical analytic estimates that
Mathlib v4.27.0 does not (yet) provide in the form the BFV proof
consumes. -/

/-- Mertens / Euler-product weighted-sum bound. Used by `OmegaTail`.
Same family as P694's `mertens_product`.
File: `Erdos/P202/BFV/Mertens.lean`. -/
example := @Erdos202.omega_weighted_sum_bfvz_bound

/-- Dyadic Chebyshev prime-count lower bound.
File: `Erdos/P202/BFV/Chebyshev.lean`. -/
example := @Erdos202.dyadicPrimeInterval_card_lower_bound

/-- BFV PDF Lemma 3.2: rarity of large hExp values via Rankin/squarefull.
File: `Erdos/P202/BFV/HExpRare.lean`. -/
example := @Erdos202.hExp_rare_count_rankin_squarefull

/-- BFV PDF Lemma 3.3: radical multiplicity bound.
File: `Erdos/P202/BFV/RadMultiplicity.lean`. -/
example := @Erdos202.rad_multiplicity_bfv33

/-! ### §3.3 BFV layer — bookkeeping above the analytic primitives

Local bookkeeping that uses Mathlib's existing prime-counting tools
(Chebyshev θ-bounds) plus the BFV scale algebra. -/

/-- CRT-tree encoding capacity for the BFV lower construction.
Discharges against Chebyshev upper bound + dyadic separation.
File: `Erdos/P202/BFV/LowerConstruction.lean`. -/
example := @Erdos202.lowerEncodingCapacity_eventually_analytic

/-- Tail-product cardinality lower bound for the BFV lower family.
Discharges against `dyadicPrimeInterval_card_lower_bound` + log/exp algebra.
File: `Erdos/P202/BFV/LowerConstruction.lean`. -/
example := @Erdos202.lowerChoices_card_lower_bound_eventually_analytic

/-! ### §3.4 BFV layer — residual input axioms

These two are still axioms because the corresponding theorem-shaped
versions have unfinished bookkeeping:

* `bfv_omega_count_input` — theorem version (`bfv_omega_count_theorem`)
  exists but has a `sorryAx` upstream in `OmegaExact`.
* `bfv_pruning_input` — theorem version (`bfv_pruning_theorem`) is
  currently a rename of the axiom; real discharge requires combining
  `bfv_omega_tail_theorem + hExp_rare_count_rankin_squarefull +
  rad_multiplicity_bfv33 + choose_one_per_fiber_card_lower` into a
  `PrunedData` witness. -/

/-- BFV omega-count input. -/
example := @Erdos202.bfv_omega_count_input

/-- BFV pruning input (PDF Proposition 3.1). -/
example := @Erdos202.bfv_pruning_input

end TrustBoundary

/-! ## §4 Axiom audit

Uncomment to verify the trust boundary. Expected output is exactly:

  `Erdos202.erdos202_main` depends on axioms:
    [propext, Classical.choice, Quot.sound,                 -- Lean core
     Erdos202.bfv_omega_count_input,                        -- §3.4
     Erdos202.bfv_pruning_input,                            -- §3.4
     Erdos202.lowerEncodingCapacity_eventually_analytic,    -- §3.3
     Erdos202.lowerChoices_card_lower_bound_eventually_analytic, -- §3.3
     Erdos202.ParkPham.CKK_const,                           -- §3.1
     Erdos202.ParkPham.CKK_const_pos,                       -- §3.1
     Erdos202.ParkPham.park_pham_threshold,                 -- §3.1
     Erdos202.ParkPham.partition_density_to_disjoint_members] -- §3.1

The §3.2 axioms (Mertens, Chebyshev dyadic, HExpRare, RadMultiplicity)
do NOT appear directly in the audit of `erdos202_main` because they are
already absorbed into `bfv_omega_count_input` and the
`lowerEncodingCapacity/Choices_card_*_analytic` pair. They are listed in
§3.2 as the genuine analytic primitives behind those higher-level inputs. -/

-- #print axioms erdos202_sharp_asymptotic

end Erdos202.Compressed
