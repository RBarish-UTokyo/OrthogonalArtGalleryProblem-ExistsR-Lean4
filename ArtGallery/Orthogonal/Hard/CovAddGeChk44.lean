module

public import ArtGallery.Orthogonal.Hard.CovAddGeData
public import ArtGallery.Orthogonal.Hard.CovSplit

/-! # Coverage certificate checks of `gCovAddGe`, part 44 (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gCovAddGe_trees32 : idxAll gCovAddGe.treeIB 384 396 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gCovAddGe_trees33 : idxAll gCovAddGe.treeIB 396 408 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gCovAddGe_trees34 : idxAll gCovAddGe.treeIB 408 411 = true := by decide +kernel

end

end ArtGallery.Orthogonal.Hard
