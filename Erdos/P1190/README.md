# Erdős Problem 1190

This directory contains the formal proof of Erdős Problem 1190 as a
real-analysis/bookkeeping corollary of the Erdős 202 theorem.

## Files

| File | Purpose |
| --- | --- |
| [`Proof.lean`](Proof.lean) | Full Lean proof of `Erdos202.erdos1190_main`. |
| [`safeverify/Spec.lean`](safeverify/Spec.lean) | SafeVerify target surface for Problem 1190. |
| [`safeverify/Safe.lean`](safeverify/Safe.lean) | SafeVerify submission wrapper importing `Erdos.P1190.Proof`. |

`Erdos/P202/P1190.lean` remains as a compatibility import of
`Erdos.P1190.Proof`.

## Main Theorem

```lean
theorem Erdos202.erdos1190_main :
  Erdos202.HasErdos1190Asymptotic
```

The theorem proves the PDF Corollary 1.2 form
`epsilon_m = exp (-(1 + o(1)) * sqrt (log m * log log m))`, where
`epsilon_m` is formalized as the supremum of reciprocal sums over finite
tail-admissible families of pairwise disjoint residue classes.

## Verification

Build the proof and SafeVerify wrapper:

```bash
lake build Erdos.P1190.Proof Erdos.P1190.safeverify.Safe
```

Build the SafeVerify target:

```bash
lake env lean -o Erdos/P1190/safeverify/Spec.olean \
  Erdos/P1190/safeverify/Spec.lean
```

Run SafeVerify from a checkout of `SafeVerify` using the same Lean toolchain:

```bash
cd /path/to/SafeVerify
LEAN_PATH="/path/to/erdos-formalizations/.lake/build/lib/lean:$(lake env printenv LEAN_PATH)" \
  lake exe safe_verify --verbose --disallow-partial \
    /path/to/erdos-formalizations/Erdos/P1190/safeverify/Spec.olean \
    /path/to/erdos-formalizations/.lake/build/lib/lean/Erdos/P1190/safeverify/Safe.olean
```

Expected output:

```text
SafeVerify check passed.
```

Axiom audit:

```text
Erdos202.erdos1190_main depends on axioms:
[propext, Classical.choice, Quot.sound]
```

