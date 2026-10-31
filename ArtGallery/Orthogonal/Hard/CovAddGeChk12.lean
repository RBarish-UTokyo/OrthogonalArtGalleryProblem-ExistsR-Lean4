module

public import ArtGallery.Orthogonal.Hard.CovAddGeData
public import ArtGallery.Orthogonal.Hard.CovKeysAddGe
public import ArtGallery.Orthogonal.Hard.CovSplit

/-! # Coverage certificate checks of `gCovAddGe`, part 12 (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gCovAddGe_items53 : idxAll gCovAddGe.itemB 159 162 = true :=
  idxAll_itemB_of_K keysCovAddGeF_ok keysCovAddGeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddGe_items54 : idxAll gCovAddGe.itemB 162 165 = true :=
  idxAll_itemB_of_K keysCovAddGeF_ok keysCovAddGeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddGe_items55 : idxAll gCovAddGe.itemB 165 168 = true :=
  idxAll_itemB_of_K keysCovAddGeF_ok keysCovAddGeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddGe_items56 : idxAll gCovAddGe.itemB 168 171 = true :=
  idxAll_itemB_of_K keysCovAddGeF_ok keysCovAddGeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddGe_items57 : idxAll gCovAddGe.itemB 171 174 = true :=
  idxAll_itemB_of_K keysCovAddGeF_ok keysCovAddGeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddGe_items58 : idxAll gCovAddGe.itemB 174 177 = true :=
  idxAll_itemB_of_K keysCovAddGeF_ok keysCovAddGeI_ok (by decide +kernel)
    (by decide +kernel)

end

end ArtGallery.Orthogonal.Hard
