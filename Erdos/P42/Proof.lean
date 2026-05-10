/-
Erdős Problem 42 — active proof umbrella.

The currently active public proof uses the Fourier-positive route. The compact
Cayley route is kept separately in `CompactCayley/Proof.lean`.

`FourierPositive/Proof.lean` remains a standalone flat snapshot. The
compact-Cayley entry point is now a modular wrapper over the axiom-free Route B
proof, so this umbrella continues to import `FC/Shape.lean` directly as the
active public route.
-/

import Erdos.P42.FC.Shape
