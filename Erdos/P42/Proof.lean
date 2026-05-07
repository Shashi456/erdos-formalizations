/-
Erdős Problem 42 — Sidon difference avoidance.

**Cayley-route umbrella file** that imports the modules used by the active
formalization of the public #42 statement:

  Erdos.P42.Basic                      — DiffFinset, SymmetricFinset,
                                         AvoidsNonzeroDiff.
  Erdos.P42.Sidon                      — IsSidonInt / IsSidonNat / IsSidonZMod,
                                         elementary cardinality lemmas.
  Erdos.P42.FourierAPI                 — normalized `ZMod.dft` predicates used
                                         by the Fourier hypotheses.
  Erdos.P42.CompactCayley.Axiom        — Route B trust boundary
                                         (`compact_cayley_clique`).
  Erdos.P42.CompactCayley.Internal     — finite tuple-to-clique endpoint for
                                         opening the compact-Cayley axiom.
  Erdos.P42.CompactCayley.Application  — Route B downstream proof of
                                         Theorem 1.1.
  Erdos.P42.FCWrapper                  — Set-ℕ statements + FC alignment
                                         (`theorem_1_1`, `IsMaximalSidonSetIn`,
                                         `erdos_42`).

Following the compact Cayley graph route from `erdos42_compact_sidon_clean.pdf`:
dense Cayley graphs on `ZMod p` with small Fourier upper bound contain large
cliques, and the downstream Sidon extraction is finite combinatorics.

The alternate Fourier-positive scaffold remains in `Erdos/P42/FourierPositive`,
but is not imported here because this file certifies the Cayley-route proof.
-/

import Erdos.P42.Basic
import Erdos.P42.Sidon
import Erdos.P42.FourierAPI
import Erdos.P42.CompactCayley.Axiom
import Erdos.P42.CompactCayley.Internal
import Erdos.P42.CompactCayley.Application
import Erdos.P42.FCWrapper
