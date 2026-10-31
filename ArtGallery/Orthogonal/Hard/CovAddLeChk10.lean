module

public import ArtGallery.Orthogonal.Hard.CovAddLeData
public import ArtGallery.Orthogonal.Hard.CovKeysAddLe
public import ArtGallery.Orthogonal.Hard.CovSplit

/-! # Coverage certificate checks of `gCovAddLe`, part 10 (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gCovAddLe_items42 : idxAll gCovAddLe.itemB 126 129 = true :=
  idxAll_itemB_of_K keysCovAddLeF_ok keysCovAddLeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddLe_items43 : idxAll gCovAddLe.itemB 129 132 = true :=
  idxAll_itemB_of_K keysCovAddLeF_ok keysCovAddLeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddLe_items44 : idxAll gCovAddLe.itemB 132 135 = true :=
  idxAll_itemB_of_K keysCovAddLeF_ok keysCovAddLeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddLe_items45 : idxAll gCovAddLe.itemB 135 138 = true :=
  idxAll_itemB_of_K keysCovAddLeF_ok keysCovAddLeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddLe_items46 : idxAll gCovAddLe.itemB 138 141 = true :=
  idxAll_itemB_of_K keysCovAddLeF_ok keysCovAddLeI_ok (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gCovAddLe_items47 : idxAll gCovAddLe.itemB 141 144 = true :=
  idxAll_itemB_of_K keysCovAddLeF_ok keysCovAddLeI_ok (by decide +kernel)
    (by decide +kernel)

end

end ArtGallery.Orthogonal.Hard
