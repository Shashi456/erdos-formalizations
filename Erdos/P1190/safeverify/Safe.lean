/-
SafeVerify submission wrapper for Erdős Problem 1190.

The external contract is `safeverify/Spec.lean`.  This file imports the
standalone 1190 proof module so SafeVerify can compare the contract
declarations against the replayed proof environment.
-/

import Mathlib
import Erdos.P1190.Proof

