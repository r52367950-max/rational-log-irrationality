# Lean verification environment

Verified with Lean 4.24.0 (release commit
`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`) and mathlib4 tag `v4.24.0`,
commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`.

Official Lean binary release:
https://github.com/leanprover/lean4/releases/download/v4.24.0/lean-4.24.0-linux.tar.zst

Official mathlib repository:
https://github.com/leanprover-community/mathlib4

Mathlib source was not modified. Its imported modules were obtained from the
official cache, matching the pinned source and compiler hashes. Only imported
module graphs were required; the full Mathlib aggregate was not compiled.

The portable project's `lean-toolchain`, `lakefile.lean`, and
`lake-manifest.json` provide the ordinary reproducible environment. On a
standard Linux machine with elan, run `lake exe cache get`, then `lake build`.
Individual files can also be checked with `lake env lean FileName.lean`.

This execution container has an application-location compatibility issue:
Lean's runtime looks up `/proc/<getpid>/exe`, while the container exposes a
working `/proc/self/exe` but a differently numbered process list. The supplied
`proc_self_compat.c` replaces only `readlink` calls for the current process's
own numeric executable path with `/proc/self/exe`. It changes neither Lean's
kernel nor any arithmetic, theorem, proof term, or imported module. A standard
machine does not require this compatibility shim.

Compilation logs contain `#print axioms` for the formalized theorems. Successful
proofs use only mathlib's usual Lean axioms (`propext`, `Classical.choice`,
`Quot.sound`); they do not use `sorryAx` or added global axioms. Hypotheses in a
conditional theorem remain explicit arguments and must separately be proved.

The artifacts verify specified parts of the manuscripts. They do not assert
that geometric Theorem A, its universal interpolation conclusion, or the
complete irrationality-exponent theorem has been formalized.
