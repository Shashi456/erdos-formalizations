# SafeVerify check

[`SafeVerify`](https://github.com/GasStationManager/SafeVerify) is a stronger
proof-checker than `lake build`: it replays every declaration through the
kernel via `Environment.replay`, enforces a hard allow-list of axioms, and
bans `partial` / `unsafe` constants. Adapted from `lean4checker`.

## Result

`Erdos/P694/Proof.lean` passes SafeVerify against the spec in `Spec.lean`,
with `--disallow-partial`. See [`safeverify_report.json`](safeverify_report.json):

| Declaration | Kind | Axioms beyond `{propext, Quot.sound, Classical.choice}` |
|---|---|---|
| `Erdos694.R` | def | — |
| `Erdos694.permanence_step` | theorem | — |
| `Erdos694.infinitely_many_collisions` | theorem | — |
| `Erdos694.totient_fibre_extremes` | theorem | `mertens_product`, `linnik_dvd` |
| `Erdos694.erdos_694_asymptotic` | theorem | `mertens_product`, `linnik_dvd` |

## Reproduce

Requires a local clone of SafeVerify pinned to the same Lean toolchain
(`leanprover/lean4:v4.27.0`, matching this repo's `lean-toolchain`).

```bash
# 1. Build this repo (produces Erdos/P694/Proof.olean under .lake/build/lib/lean/).
lake build

# 2. Build the SafeVerify spec to .olean.
lake env lean -o safeverify/Spec.olean safeverify/Spec.lean

# 3. In your SafeVerify clone, extend `allowedAxioms` in `Main.lean` to
#    accept our two named axioms — both are classical, unconditional results
#    that Mathlib has not yet bundled into named lemmas:
#
#      allowedAxioms := #[`propext, `Quot.sound, `Classical.choice,
#        `Erdos694.mertens_product, `Erdos694.linnik_dvd]
#
#    Then `lake build && lake exe cache get` in the SafeVerify clone.

# 4. Run the check.
cd /path/to/SafeVerify
lake exe safe_verify --verbose --disallow-partial \
  -s /path/to/erdos-formalizations/safeverify/safeverify_report.json \
  /path/to/erdos-formalizations/safeverify/Spec.olean \
  /path/to/erdos-formalizations/.lake/build/lib/lean/Erdos/P694/Proof.olean
```

Expected output ends with `SafeVerify check passed.`

## Why is this stronger than `lake build` + `#print axioms`?

`lake build` confirms type-checking. `#print axioms` lists axioms but runs
inside the same kernel session as the proof — a sufficiently exotic tactic
could in principle inject axioms through environment manipulation that
`#print axioms` would miss. SafeVerify replays from `.olean`, then runs the
axiom check on the replayed environment, defending against both classes of
issue. It also enforces a hard allow-list (rejects unexpected axioms by
default) and rejects `partial` / `unsafe` constants.
