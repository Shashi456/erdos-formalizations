/-
Erdős Problem 42 — compact-Cayley route umbrella.

This file keeps Route B separate from the active Fourier-positive proof. It
imports the common finite machinery and the compact-Cayley trust boundary
`compact_cayley_clique`, then exposes
`Erdos42.CompactCayley.theorem_1_1_from_compact_cayley`.

It intentionally does not import `FCWrapper.lean`, because the public wrapper is
currently routed through `Proof_Fourier.lean`.
-/

import Erdos.P42.Basic
import Erdos.P42.Sidon
import Erdos.P42.FourierAPI
import Erdos.P42.CompactCayley.Axiom
import Erdos.P42.CompactCayley.Application
import Erdos.P42.CompactCayley.RouteB
