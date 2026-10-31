module

public import ArtGallery.Orthogonal.Hard.CovAddLeData
public import ArtGallery.Orthogonal.Hard.CovKeysAddLe
public import ArtGallery.Orthogonal.Hard.CovSplit

/-! # Coverage certificate checks of `gCovAddLe`, part 19 (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gCovAddLe_items96 : idxAll gCovAddLe.itemB 288 291 = true :=
  idxAll_itemB_of_K keysCovAddLeF_ok keysCovAddLeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddLe_items97 : idxAll gCovAddLe.itemB 291 294 = true :=
  idxAll_itemB_of_K keysCovAddLeF_ok keysCovAddLeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddLe_items98 : idxAll gCovAddLe.itemB 294 297 = true :=
  idxAll_itemB_of_K keysCovAddLeF_ok keysCovAddLeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddLe_items99 : idxAll gCovAddLe.itemB 297 300 = true :=
  idxAll_itemB_of_K keysCovAddLeF_ok keysCovAddLeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddLe_items100 : idxAll gCovAddLe.itemB 300 303 = true :=
  idxAll_itemB_of_K keysCovAddLeF_ok keysCovAddLeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddLe_items101 : idxAll gCovAddLe.itemB 303 306 = true :=
  idxAll_itemB_of_K keysCovAddLeF_ok keysCovAddLeI_ok (by decide +kernel)
    (by decide +kernel)

end

end ArtGallery.Orthogonal.Hard
