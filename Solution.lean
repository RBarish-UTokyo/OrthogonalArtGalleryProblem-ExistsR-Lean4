module

public import ArtGallery.Orthogonal.MembershipMain
public import ArtGallery.Orthogonal.MainTheorems

/-!
# Solution

Imports the proof development; the advertised theorems of `Challenge.lean` are the declarations
of the same names (namespace `ArtGallery`) proved in the library:

* `agpOrth_inER`, `agpOrthPointBoundary_inER` and their guard-variable forms
  `agpOrth_inER_guard_variables`, `agpOrthPointBoundary_inER_guard_variables` (membership in
  `∃ℝ`, by formulas in the `2g` guard coordinates) — `ArtGallery/Orthogonal/MembershipMain.lean`
* `agpOrth_erComplete`, `agpOrthPointBoundary_erComplete` (`∃ℝ`-completeness for orthogonal
  polygons, point-point and point-boundary) — `ArtGallery/Orthogonal/MainTheorems.lean`, through
  the orthogonal construction (`ArtGallery/Orthogonal/Hard/`)
-/
