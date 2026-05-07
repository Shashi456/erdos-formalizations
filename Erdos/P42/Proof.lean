/-
Erdős Problem 42 — active proof umbrella.

The currently active public proof uses the Fourier-positive route. The compact
Cayley route is kept separately in `CompactCayley/Proof.lean`.

`FourierPositive/Proof.lean` and `CompactCayley/Proof.lean` are standalone flat
snapshots, so this modular umbrella imports `FC/Shape.lean` directly
to avoid duplicate declarations when the full project is built.
-/

import Erdos.P42.FC.Shape
