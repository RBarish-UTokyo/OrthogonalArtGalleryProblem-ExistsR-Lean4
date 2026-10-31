module

public import ArtGallery.Orthogonal.Hard.CovAddLeData
public import ArtGallery.Orthogonal.Hard.CovKeysAddLe
public import ArtGallery.Orthogonal.Hard.CovSplit

/-! # Coverage certificate checks of `gCovAddLe`, part 8 (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gCovAddLe_items30 : idxAll gCovAddLe.itemB 90 93 = true :=
  idxAll_itemB_of_K keysCovAddLeF_ok keysCovAddLeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddLe_items31 : idxAll gCovAddLe.itemB 93 96 = true :=
  idxAll_itemB_of_K keysCovAddLeF_ok keysCovAddLeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddLe_items32 : idxAll gCovAddLe.itemB 96 99 = true :=
  idxAll_itemB_of_K keysCovAddLeF_ok keysCovAddLeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddLe_items33 : idxAll gCovAddLe.itemB 99 102 = true :=
  idxAll_itemB_of_K keysCovAddLeF_ok keysCovAddLeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddLe_items34 : idxAll gCovAddLe.itemB 102 105 = true :=
  idxAll_itemB_of_K keysCovAddLeF_ok keysCovAddLeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddLe_items35 : idxAll gCovAddLe.itemB 105 108 = true :=
  idxAll_itemB_of_K keysCovAddLeF_ok keysCovAddLeI_ok (by decide +kernel)
    (by decide +kernel)

end

end ArtGallery.Orthogonal.Hard
