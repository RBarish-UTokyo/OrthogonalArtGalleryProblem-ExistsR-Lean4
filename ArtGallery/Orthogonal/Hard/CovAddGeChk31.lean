module

public import ArtGallery.Orthogonal.Hard.CovAddGeData
public import ArtGallery.Orthogonal.Hard.CovKeysAddGe
public import ArtGallery.Orthogonal.Hard.CovSplit

/-! # Coverage certificate checks of `gCovAddGe`, part 31 (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gCovAddGe_items167 : idxAll gCovAddGe.itemB 501 504 = true :=
  idxAll_itemB_of_K keysCovAddGeF_ok keysCovAddGeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddGe_items168 : idxAll gCovAddGe.itemB 504 507 = true :=
  idxAll_itemB_of_K keysCovAddGeF_ok keysCovAddGeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddGe_items169 : idxAll gCovAddGe.itemB 507 510 = true :=
  idxAll_itemB_of_K keysCovAddGeF_ok keysCovAddGeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddGe_rngs0 : idxAll gCovAddGe.rngB 0 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gCovAddGe_rngs1 : idxAll gCovAddGe.rngB 12 24 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gCovAddGe_rngs2 : idxAll gCovAddGe.rngB 24 36 = true := by decide +kernel

end

end ArtGallery.Orthogonal.Hard
