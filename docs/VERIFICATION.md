# Verification record

Local runs on the contents of this repository, 2026-10-31. Official Palomar verification has not
been performed.

## Environment

* Lean `leanprover/lean4:v4.35.0-rc2` (commit `11acb17ec6b07a8f9e9173e6845197929540936b`), Lake
  5.0.0, Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55` (`lake-manifest.json`).
* Independent kernels bundled with the toolchain: NanoDa (`nanoda_bin` 0.4.17) and con-ron.
* A Linux cloud container with 4 virtual CPUs and 15 GB of memory.

## Build

```sh
lake exe cache get
lake build
```

Result: `Build completed successfully (9621 jobs)`, in about 37 minutes with the Mathlib cache.
The build reports deprecation warnings only.

## Comparator

```sh
lake comparator --config comparator.json
```

with `nanoda_bin` on `PATH`. The configuration names the six theorems of `Challenge.lean`, permits
the axioms `propext`, `Quot.sound` and `Classical.choice`, and enables NanoDa.

Result (6,830 s including the build check and the export):

```
Running nanoda kernel on solution
nanoda kernel accepts the solution
Running Lean default kernel on solution
Lean default kernel accepts the solution
Your solution is okay!
```

## con-ron

The same six theorems and the three axioms, exported with `lake env leanexport Solution -- …` and
checked by the toolchain's con-ron with four workers:

```sh
con-ron --jobs=4 export.ndjson
```

Result: `con-ron: accepted 47435 declarations (--verified)`, in 2,482 s with a peak resident set
of 8.9 GB.

## Axioms

The comparator checks that the six theorems use no axioms other than `propext`, `Quot.sound` and
`Classical.choice`. The sources contain no `sorry`, no other `axiom` and no `native_decide`; the
large finite computations are checked by the kernel (`decide +kernel`).
