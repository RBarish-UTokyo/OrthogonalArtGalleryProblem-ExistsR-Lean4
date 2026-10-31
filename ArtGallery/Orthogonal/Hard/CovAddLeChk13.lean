module

public import ArtGallery.Orthogonal.Hard.CovAddLeData
public import ArtGallery.Orthogonal.Hard.CovKeysAddLe
public import ArtGallery.Orthogonal.Hard.CovSplit

/-! # Coverage certificate checks of `gCovAddLe`, part 13 (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gCovAddLe_items60 : idxAll gCovAddLe.itemB 180 183 = true :=
  idxAll_itemB_of_K keysCovAddLeF_ok keysCovAddLeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddLe_items61 : idxAll gCovAddLe.itemB 183 186 = true :=
  idxAll_itemB_of_K keysCovAddLeF_ok keysCovAddLeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddLe_items62 : idxAll gCovAddLe.itemB 186 189 = true :=
  idxAll_itemB_of_K keysCovAddLeF_ok keysCovAddLeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddLe_items63 : idxAll gCovAddLe.itemB 189 192 = true :=
  idxAll_itemB_of_K keysCovAddLeF_ok keysCovAddLeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddLe_items64 : idxAll gCovAddLe.itemB 192 195 = true :=
  idxAll_itemB_of_K keysCovAddLeF_ok keysCovAddLeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddLe_items65 : idxAll gCovAddLe.itemB 195 198 = true :=
  idxAll_itemB_of_K keysCovAddLeF_ok keysCovAddLeI_ok (by decide +kernel)
    (by decide +kernel)

end

end ArtGallery.Orthogonal.Hard
