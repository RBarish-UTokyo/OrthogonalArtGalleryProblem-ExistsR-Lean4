module

public import ArtGallery.Orthogonal.Hard.CovAddGeData
public import ArtGallery.Orthogonal.Hard.CovKeysAddGe
public import ArtGallery.Orthogonal.Hard.CovSplit

/-! # Coverage certificate checks of `gCovAddGe`, part 7 (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gCovAddGe_items23 : idxAll gCovAddGe.itemB 69 72 = true :=
  idxAll_itemB_of_K keysCovAddGeF_ok keysCovAddGeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddGe_items24 : idxAll gCovAddGe.itemB 72 75 = true :=
  idxAll_itemB_of_K keysCovAddGeF_ok keysCovAddGeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddGe_items25 : idxAll gCovAddGe.itemB 75 78 = true :=
  idxAll_itemB_of_K keysCovAddGeF_ok keysCovAddGeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddGe_items26 : idxAll gCovAddGe.itemB 78 81 = true :=
  idxAll_itemB_of_K keysCovAddGeF_ok keysCovAddGeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddGe_items27 : idxAll gCovAddGe.itemB 81 84 = true :=
  idxAll_itemB_of_K keysCovAddGeF_ok keysCovAddGeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddGe_items28 : idxAll gCovAddGe.itemB 84 87 = true :=
  idxAll_itemB_of_K keysCovAddGeF_ok keysCovAddGeI_ok (by decide +kernel)
    (by decide +kernel)

end

end ArtGallery.Orthogonal.Hard
