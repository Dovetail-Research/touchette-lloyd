# InfoTheory

A Lean 4 library for information theory: Shannon entropy, conditional entropy,
mutual information, and (planned) ergodic-theoretic entropy (Kolmogorov–Sinai),
built on [Mathlib](https://github.com/leanprover-community/mathlib4).

The core Shannon-entropy development is vendored from the
[PFR project](https://github.com/teorth/pfr) (`PFR/ForMathlib/Entropy/`), whose
upstreaming to Mathlib is currently stalled. See [VENDORED.md](VENDORED.md) for
provenance and the rules for the vendored files (`InfoTheory/PFR/` — never edit
by hand). If/when that material lands in Mathlib, the vendored directory is
deleted and the facade `InfoTheory/Entropy.lean` is repointed at Mathlib.

## Layout

- `InfoTheory/PFR/` — vendored PFR entropy development (do not edit; see `VENDORED.md`)
- `InfoTheory/Entropy.lean` — facade re-exporting the entropy API; import this, not `InfoTheory.PFR.*`
- `InfoTheory/Shannon/` — original Shannon-theory material
- `InfoTheory/Ergodic/` — (planned) partitions, partition entropy, Kolmogorov–Sinai entropy

## Building

```
lake exe cache get   # download prebuilt Mathlib artifacts (several GB, first time only)
lake build
```

The toolchain and Mathlib pin are kept identical to PFR's current pins; when
bumping Mathlib, follow PFR's pin bumps and re-run `scripts/vendor.sh` (see
`VENDORED.md`) — never bump Mathlib independently while vendored files remain.
