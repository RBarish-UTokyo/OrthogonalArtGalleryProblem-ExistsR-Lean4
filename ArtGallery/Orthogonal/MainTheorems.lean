module

public import ArtGallery.Orthogonal.MembershipMain
public import ArtGallery.Orthogonal.Hard.MainO

/-!
# The orthogonal art gallery problems are ∃ℝ-complete

Membership (`ArtGallery/Orthogonal/MembershipMain.lean`) and hardness by the orthogonal
construction (`ArtGallery/Orthogonal/Hard/`): Stade's polygon
in which every non-axis-parallel edge has been replaced by orthogonal features, with helper guards
pinned by needle cutters (`ArtGallery.Orthogonal.Hard.etr_polyRed_agpOrth`,
`ArtGallery.Orthogonal.Hard.etr_polyRed_agpOrthPointBoundary`).
-/

@[expose] public section

namespace ArtGallery

open Complexity

/-- **The orthogonal art gallery problem is `∃ℝ`-complete.** -/
theorem agpOrth_erComplete : ERComplete AGPOrth :=
  ERComplete.of_polyRed_ETR agpOrth_inER Orthogonal.Hard.etr_polyRed_agpOrth

/-- **The orthogonal point-boundary art gallery problem is `∃ℝ`-complete.** -/
theorem agpOrthPointBoundary_erComplete : ERComplete AGPOrthPointBoundary :=
  ERComplete.of_polyRed_ETR agpOrthPointBoundary_inER Orthogonal.Hard.etr_polyRed_agpOrthPointBoundary

end ArtGallery

end
