module

public import ArtGallery.Orthogonal.Hard.SpotCertsAddLe
public import ArtGallery.Orthogonal.Hard.SpotCertsAddLeHints
public import ArtGallery.Orthogonal.Hard.PropKeysD
public import ArtGallery.Orthogonal.Hard.SpotSplit

/-! # Spot certificate check of the helper `8` of the group `slot addLe` (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gAddLeSC5_head : spotHeadB (slotD .addLe) 8 gAddLeSC5T = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeSC5_base : (gAddLeSC5T.cert (slotD .addLe).gs).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeSC5_p0 : (gAddLeSC5T.cert (slotD .addLe).gs).okPropR 0 50 = true :=
  TCertI.okPropR_of_K gAddLeSC5I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC5H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC5_p50 : (gAddLeSC5T.cert (slotD .addLe).gs).okPropR 50 100 = true :=
  TCertI.okPropR_of_K gAddLeSC5I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC5H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC5_p100 : (gAddLeSC5T.cert (slotD .addLe).gs).okPropR 100 150 = true :=
  TCertI.okPropR_of_K gAddLeSC5I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC5H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC5_p150 : (gAddLeSC5T.cert (slotD .addLe).gs).okPropR 150 200 = true :=
  TCertI.okPropR_of_K gAddLeSC5I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC5H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC5_p200 : (gAddLeSC5T.cert (slotD .addLe).gs).okPropR 200 250 = true :=
  TCertI.okPropR_of_K gAddLeSC5I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC5H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC5_p250 : (gAddLeSC5T.cert (slotD .addLe).gs).okPropR 250 300 = true :=
  TCertI.okPropR_of_K gAddLeSC5I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC5H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC5_p300 : (gAddLeSC5T.cert (slotD .addLe).gs).okPropR 300 350 = true :=
  TCertI.okPropR_of_K gAddLeSC5I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC5H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC5_p350 : (gAddLeSC5T.cert (slotD .addLe).gs).okPropR 350 397 = true :=
  TCertI.okPropR_of_K gAddLeSC5I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC5H (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The spot check of the helper `8` of the group `slot addLe`. -/
theorem gAddLeSC5T_ok : spotFarB (slotD .addLe) 8 gAddLeSC5T = true :=
  spotFarB_of_parts gAddLeSC5_head (LCert.ok_of_parts gAddLeSC5_base (n := 397) (by decide +kernel)
    (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) gAddLeSC5_p0 gAddLeSC5_p50) gAddLeSC5_p100) gAddLeSC5_p150) gAddLeSC5_p200) gAddLeSC5_p250) gAddLeSC5_p300) gAddLeSC5_p350))

end

end ArtGallery.Orthogonal.Hard
