/-
SafeVerify submission wrapper for Erdős Problem 202.

The external contract is `safeverify/Spec.lean`.  This file imports the
standalone flat proof bundle so SafeVerify can compare the contract
declarations against the replayed proof environment without rechecking every
internal declaration in the flat file as a new submitted declaration.
-/

import Mathlib
import Erdos.P202.Proof
