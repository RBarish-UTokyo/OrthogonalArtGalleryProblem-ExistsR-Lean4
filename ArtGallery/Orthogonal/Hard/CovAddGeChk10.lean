module

public import ArtGallery.Orthogonal.Hard.CovAddGeData
public import ArtGallery.Orthogonal.Hard.CovKeysAddGe
public import ArtGallery.Orthogonal.Hard.CovSplit

/-! # Coverage certificate checks of `gCovAddGe`, part 10 (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gCovAddGe_items41 : idxAll gCovAddGe.itemB 123 126 = true :=
  idxAll_itemB_of_K keysCovAddGeF_ok keysCovAddGeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddGe_items42 : idxAll gCovAddGe.itemB 126 129 = true :=
  idxAll_itemB_of_K keysCovAddGeF_ok keysCovAddGeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddGe_items43 : idxAll gCovAddGe.itemB 129 132 = true :=
  idxAll_itemB_of_K keysCovAddGeF_ok keysCovAddGeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddGe_items44 : idxAll gCovAddGe.itemB 132 135 = true :=
  idxAll_itemB_of_K keysCovAddGeF_ok keysCovAddGeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddGe_items45 : idxAll gCovAddGe.itemB 135 138 = true :=
  idxAll_itemB_of_K keysCovAddGeF_ok keysCovAddGeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddGe_items46 : idxAll gCovAddGe.itemB 138 141 = true :=
  idxAll_itemB_of_K keysCovAddGeF_ok keysCovAddGeI_ok (by decide +kernel)
    (by decide +kernel)

end

end ArtGallery.Orthogonal.Hard
