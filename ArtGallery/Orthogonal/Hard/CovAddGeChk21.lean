module

public import ArtGallery.Orthogonal.Hard.CovAddGeData
public import ArtGallery.Orthogonal.Hard.CovKeysAddGe
public import ArtGallery.Orthogonal.Hard.CovSplit

/-! # Coverage certificate checks of `gCovAddGe`, part 21 (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gCovAddGe_items107 : idxAll gCovAddGe.itemB 321 324 = true :=
  idxAll_itemB_of_K keysCovAddGeF_ok keysCovAddGeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddGe_items108 : idxAll gCovAddGe.itemB 324 327 = true :=
  idxAll_itemB_of_K keysCovAddGeF_ok keysCovAddGeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddGe_items109 : idxAll gCovAddGe.itemB 327 330 = true :=
  idxAll_itemB_of_K keysCovAddGeF_ok keysCovAddGeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddGe_items110 : idxAll gCovAddGe.itemB 330 333 = true :=
  idxAll_itemB_of_K keysCovAddGeF_ok keysCovAddGeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddGe_items111 : idxAll gCovAddGe.itemB 333 336 = true :=
  idxAll_itemB_of_K keysCovAddGeF_ok keysCovAddGeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddGe_items112 : idxAll gCovAddGe.itemB 336 339 = true :=
  idxAll_itemB_of_K keysCovAddGeF_ok keysCovAddGeI_ok (by decide +kernel)
    (by decide +kernel)

end

end ArtGallery.Orthogonal.Hard
