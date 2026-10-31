module

public import ArtGallery.Orthogonal.Hard.CovAddGeData
public import ArtGallery.Orthogonal.Hard.CovKeysAddGe
public import ArtGallery.Orthogonal.Hard.CovSplit

/-! # Coverage certificate checks of `gCovAddGe`, part 3 (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gCovAddGe_fz6 : idxAll (fun k => (gCovAddGe.frame.zones.getD k zoneD).ok) 6 7 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem gCovAddGe_items0 : idxAll gCovAddGe.itemB 0 3 = true :=
  idxAll_itemB_of_K keysCovAddGeF_ok keysCovAddGeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddGe_items1 : idxAll gCovAddGe.itemB 3 6 = true :=
  idxAll_itemB_of_K keysCovAddGeF_ok keysCovAddGeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddGe_items2 : idxAll gCovAddGe.itemB 6 9 = true :=
  idxAll_itemB_of_K keysCovAddGeF_ok keysCovAddGeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddGe_items3 : idxAll gCovAddGe.itemB 9 12 = true :=
  idxAll_itemB_of_K keysCovAddGeF_ok keysCovAddGeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddGe_items4 : idxAll gCovAddGe.itemB 12 15 = true :=
  idxAll_itemB_of_K keysCovAddGeF_ok keysCovAddGeI_ok (by decide +kernel)
    (by decide +kernel)

end

end ArtGallery.Orthogonal.Hard
