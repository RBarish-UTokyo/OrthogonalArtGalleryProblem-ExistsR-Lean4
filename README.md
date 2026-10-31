# The orthogonal art gallery problem is ∃ℝ-complete, in Lean 4

This repository contains a Lean 4 formalization of material in a forthcoming manuscript entitled
*The Orthogonal Art Gallery Problem is ∃ℝ-complete*.

Lean proves that the art gallery problem remains `∃ℝ`-complete for **orthogonal polygons** (every
edge horizontal or vertical), in the point-point and in the point-boundary variant, for an
explicit Turing-machine model. The general problems are treated by M. Abrahamsen, A. Adamaszek and
T. Miltzow, *The Art Gallery Problem is ∃ℝ-complete* (J. ACM 2021), and by J. Stade, *The
Point-Boundary Art Gallery Problem is ∃ℝ-hard* (SoCG 2025); the hardness proof for orthogonal
polygons is a new construction derived from Stade's polygon.

Author and maintainer: Robert D. Barish (rbarish@ims.u-tokyo.ac.jp).

* **What Lean proves.** Deciding whether an orthogonal simple polygon with rational vertex
  coordinates can be guarded by `g` guards is `∃ℝ`-complete, both when the guards must see the
  whole polygon (point-point) and when they must see only its boundary (point-boundary). Both
  problems also reduce to ETR by formulas whose only variables are the `2g` coordinates of the
  guards.
* **Axioms.** The proof uses exactly Lean's three standard axioms (`propext`,
  `Classical.choice`, `Quot.sound`). There is no `sorry`, no other axiom and no `native_decide`;
  large finite computations (visibility and coverage certificates) are checked by the kernel
  (`decide +kernel`).
* **Checking.** The Lean kernel checks the proof; Comparator checks that the solution proves the
  challenge statement and replays it with the toolchain's independent kernels (see
  [Checking](#checking)). The recorded runs are local; official Palomar verification has not been
  performed.

## The statement

The statement is [`Challenge.lean`](Challenge.lean): the definitions used by the theorems (the
machine model, ETR and `∃ℝ`, polygons, guarding, the problems), followed by six theorems in
namespace `ArtGallery`:

```lean
theorem agpOrth_erComplete : ERComplete AGPOrth                            -- point-point
theorem agpOrthPointBoundary_erComplete : ERComplete AGPOrthPointBoundary  -- point-boundary
theorem agpOrth_inER : InER AGPOrth
theorem agpOrthPointBoundary_inER : InER AGPOrthPointBoundary
theorem agpOrth_inER_guard_variables :
    ∃ f : Word → Word, PolyTime f ∧ (∀ w, AGPOrth w ↔ ETR (f w)) ∧
      ∀ (V : List FracPoint) (g : ℕ), ∃ φ : ETR.Formula,
        f (encodeAGP V g) = φ.encode ∧ φ.VarsLt (2 * g)
theorem agpOrthPointBoundary_inER_guard_variables : …                     -- the same for AGPOrthPointBoundary
```

### Definitions

All definitions are in `Challenge.lean` with docstrings.

* **Machines and complexity.** Deterministic single-tape Turing machines over
  {blank, 0, 1, separator}, time = number of steps, polynomial bounds `c * (n + 1)^k`,
  `PolyTime f`, `PolyRed A B` (polynomial-time many-one reductions). These are reused verbatim
  from the author's Palomar entry [NPC].
* **ETR.** Terms with constants `0, 1` and `+, −, ·`; quantifier-free formulas with `=, <, ≤`,
  `¬, ∧, ∨` over the variables `x₀, x₁, …`; `ETR` is the set of codes of satisfiable formulas.
  `InER L` means that `L` reduces to `ETR`; `ERHard L` means that every language in `∃ℝ` reduces
  to `L`; `ERComplete L` is both.
* **Codes.** Variable indices are written in unary; the numbers of an art gallery instance
  (numerators, denominators, `g`) are written in binary.
* **Polygons and guarding.** A polygon is its list of corners in boundary order; it is simple if
  it has at least three distinct corners and any two distinct edges meet exactly in their common
  endpoints (collinear consecutive corners are allowed). It is orthogonal if the two endpoints of
  every edge have equal first or equal second coordinates. Its region `filled` is the boundary
  together with the points whose component in the complement of the boundary is bounded. Two
  points see each other if the closed segment between them lies in the region. A guard set is a
  set of points of the region seeing every point of the region; a boundary guard set consists of
  points of the region and sees every boundary point. These definitions are those of the author's
  Palomar entry [CHZ] on Chazelle's triangulation algorithm.
* **Problems.** `AGP`: codes of a list of rational corners (numerator/denominator pairs) and a
  number `g` such that the polygon is simple and has a guard set with exactly `g` points
  (equivalently at most `g`, since guards can be added). `AGPPointBoundary`: the same with
  boundary guard sets. `AGPOrth` and `AGPOrthPointBoundary`: their restrictions to orthogonal
  polygons.

## The proof

The reduction is ETR → ETR-INV ([AAM] §4) → ETR-INV-REV ([S], Theorem 2.4) → an orthogonal
polygon (`ArtGallery/Orthogonal/Hard/`). The polygon is obtained from Stade's polygon for the
point-boundary problem (`ArtGallery/Stade/`), which also works for the point-point problem, by replacing every edge that is not axis-parallel; the
additional helper guards are counted in the guard number. The proof is organised as Stade's
(lower bound, guard positions, nook algebra, coverage), with kernel-checked certificates for the
finite visibility, pinning and coverage facts of the gadgets.

Membership in `∃ℝ` is the general membership argument of [AAM] §3 in the form with `2g`
variables (`ArtGallery/FewVars/`), conjoined with a variable-free formula stating that the polygon
is orthogonal.

## Checking

The project pins Lean `leanprover/lean4:v4.35.0-rc2` and Mathlib commit
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.

```sh
lake exe cache get
lake build
lake comparator --config comparator.json
```

The committed Lean files, including the generated certificate and data files, are the only inputs;
no source-generation step is needed. `comparator.json` enables the toolchain's NanoDa kernel in
addition to Lean's kernel (`nanoda_bin` must be on `PATH`). The record of the local runs, including
a run of the toolchain's con-ron kernel, is in [`docs/VERIFICATION.md`](docs/VERIFICATION.md).

## Layout

* `Challenge.lean`, `Solution.lean`, `comparator.json`: the Palomar statement, proof and
  Comparator configuration.
* `ArtGallery/Spec.lean`, `ArtGallery/Orthogonal/Spec.lean`: every definition the statement uses
  (`ArtGallery/Spec.lean` also defines the general problems and ETR-INV, which the library uses).
* `Complexity/`, `PT/`: the machine model, a register language and a framework for proving
  polynomial time (reused from earlier entries).
* `ArtGallery/ETR/`, `ArtGallery/PTime/`: circuits, a ball theorem, the reductions
  ETR → ETR-INV → ETR-INV-REV and their polynomial-time proofs.
* `ArtGallery/Membership/`, `ArtGallery/FewVars/`: membership in `∃ℝ` with `2g` variables.
* `ArtGallery/Stade/`: Stade's construction and its generic tools (counting, rooms, nook
  algebra), on which the orthogonal construction builds.
* `ArtGallery/Orthogonal/`: the orthogonal problems, their membership, and the orthogonal
  construction (`Hard/`): the polygon, simplicity, orthogonality, the region as a union of
  rectangles, counting, pinning, soundness, completeness (coverage certificates), polynomial time
  and the final theorems (`ArtGallery/Orthogonal/MainTheorems.lean`).
* `ArtGallery/Vis/`, `ArtGallery/{Geometry, Jordan, Existence, Invariance}/`: visibility in
  polygons, planar geometry, the Jordan curve theorem for polygons, triangulations and affine
  invariance.
* `docs/`: provenance and verification records.

## Relation to the earlier entry

This repository contains the part of the author's Palomar entry [AGP] (*The Art Gallery Problem
is ∃ℝ-complete: point-point, boundary-point and point-boundary variants, in Lean 4*) that the
orthogonal theorems depend on (the ETR reductions, membership, Stade's construction and the
geometry and visibility library), together with the orthogonal problems and construction, which
are new. [`docs/PROVENANCE.md`](docs/PROVENANCE.md)
lists the origin of every Lean file. The machine model, the polynomial-time framework and part of
the complexity library come from the author's Palomar entries [NPC] and [MAX]; the polygon
definitions and the planar-geometry and Jordan-curve library are adapted from [CHZ].

AI assistance is acknowledged: Claude Opus 5.5 (Anthropic) was used for the Lean formalization
and to assist with the documentation. The generated Lean files (certificates and construction
data) were produced by development programs (exact rational arithmetic) that are not part of this
repository; all generated files are checked by the Lean kernel like all other files. See
`formalization.yaml` for the automation and review metadata.

Development date: 2026-10-30.

## References

* [AAM] M. Abrahamsen, A. Adamaszek, T. Miltzow. The art gallery problem is ∃ℝ-complete.
  Journal of the ACM 69(1), Article 4 (2021). Preliminary version STOC 2018.
* [S] J. Stade. The point-boundary art gallery problem is ∃ℝ-hard. SoCG 2025, LIPIcs 332,
  Paper 74. Full version arXiv:2210.12817.
* [AGP] R. D. Barish. The Art Gallery Problem is ∃ℝ-complete: point-point, boundary-point and
  point-boundary variants, in Lean 4. Palomar, PALOMAR-2026-10-27-000025 v1 (2026).
  <https://palomar-registry.org/entry?id=PALOMAR-2026-10-27-000025&version=1>
* [NPC] R. D. Barish. NP-completeness of SAT, 3-SAT and their variants (the Cook–Levin theorem)
  in Lean 4. Palomar, PALOMAR-2026-10-02-000013 v1 (2026).
  <https://palomar-registry.org/entry?id=PALOMAR-2026-10-02-000013&version=1>
* [MAX] R. D. Barish. MaxSNP-completeness and APX-completeness of MAX-3-SAT and 3-OCCURRENCE
  MAX-3-SAT (the PCP theorem and hardness of approximation) in Lean 4. Palomar,
  PALOMAR-2026-10-09-000010 v1 (2026).
  <https://palomar-registry.org/entry?id=PALOMAR-2026-10-09-000010&version=1>
* [CHZ] R. D. Barish. Linear-Time Triangulation of Simple Polygons (Chazelle's Algorithm) in
  Lean 4. Palomar, PALOMAR-2026-10-05-000003 v2 (2026).
  <https://palomar-registry.org/entry?id=PALOMAR-2026-10-05-000003&version=2>

## License

Apache License 2.0 ([`LICENSE`](LICENSE)). Mathlib and its dependencies retain their own
licenses.
