module

public import ArtGallery.Orthogonal.Hard.CovAddLeData
public import ArtGallery.Orthogonal.Hard.CovKeysAddLe
public import ArtGallery.Orthogonal.Hard.CovSplit

/-! # Coverage certificate checks of `gCovAddLe`, part 3 (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gCovAddLe_items0 : idxAll gCovAddLe.itemB 0 3 = true :=
  idxAll_itemB_of_K keysCovAddLeF_ok keysCovAddLeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddLe_items1 : idxAll gCovAddLe.itemB 3 6 = true :=
  idxAll_itemB_of_K keysCovAddLeF_ok keysCovAddLeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddLe_items2 : idxAll gCovAddLe.itemB 6 9 = true :=
  idxAll_itemB_of_K keysCovAddLeF_ok keysCovAddLeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddLe_items3 : idxAll gCovAddLe.itemB 9 12 = true :=
  idxAll_itemB_of_K keysCovAddLeF_ok keysCovAddLeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddLe_items4 : idxAll gCovAddLe.itemB 12 15 = true :=
  idxAll_itemB_of_K keysCovAddLeF_ok keysCovAddLeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddLe_items5 : idxAll gCovAddLe.itemB 15 18 = true :=
  idxAll_itemB_of_K keysCovAddLeF_ok keysCovAddLeI_ok (by decide +kernel)
    (by decide +kernel)

end

end ArtGallery.Orthogonal.Hard
