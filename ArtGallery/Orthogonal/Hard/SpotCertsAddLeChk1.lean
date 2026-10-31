module

public import ArtGallery.Orthogonal.Hard.SpotCertsAddLe
public import ArtGallery.Orthogonal.Hard.SpotCertsAddLeHints
public import ArtGallery.Orthogonal.Hard.PropKeysD
public import ArtGallery.Orthogonal.Hard.SpotSplit

/-! # Spot certificate check of the helper `3` of the group `slot addLe` (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gAddLeSC1_head : spotHeadB (slotD .addLe) 3 gAddLeSC1T = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeSC1_base : (gAddLeSC1T.cert (slotD .addLe).gs).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeSC1_p0 : (gAddLeSC1T.cert (slotD .addLe).gs).okPropR 0 50 = true :=
  TCertI.okPropR_of_K gAddLeSC1I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC1H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC1_p50 : (gAddLeSC1T.cert (slotD .addLe).gs).okPropR 50 100 = true :=
  TCertI.okPropR_of_K gAddLeSC1I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC1H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC1_p100 : (gAddLeSC1T.cert (slotD .addLe).gs).okPropR 100 150 = true :=
  TCertI.okPropR_of_K gAddLeSC1I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC1H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC1_p150 : (gAddLeSC1T.cert (slotD .addLe).gs).okPropR 150 200 = true :=
  TCertI.okPropR_of_K gAddLeSC1I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC1H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC1_p200 : (gAddLeSC1T.cert (slotD .addLe).gs).okPropR 200 250 = true :=
  TCertI.okPropR_of_K gAddLeSC1I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC1H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC1_p250 : (gAddLeSC1T.cert (slotD .addLe).gs).okPropR 250 300 = true :=
  TCertI.okPropR_of_K gAddLeSC1I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC1H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC1_p300 : (gAddLeSC1T.cert (slotD .addLe).gs).okPropR 300 350 = true :=
  TCertI.okPropR_of_K gAddLeSC1I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC1H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC1_p350 : (gAddLeSC1T.cert (slotD .addLe).gs).okPropR 350 397 = true :=
  TCertI.okPropR_of_K gAddLeSC1I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC1H (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The spot check of the helper `3` of the group `slot addLe`. -/
theorem gAddLeSC1T_ok : spotFarB (slotD .addLe) 3 gAddLeSC1T = true :=
  spotFarB_of_parts gAddLeSC1_head (LCert.ok_of_parts gAddLeSC1_base (n := 397) (by decide +kernel)
    (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) gAddLeSC1_p0 gAddLeSC1_p50) gAddLeSC1_p100) gAddLeSC1_p150) gAddLeSC1_p200) gAddLeSC1_p250) gAddLeSC1_p300) gAddLeSC1_p350))

end

end ArtGallery.Orthogonal.Hard
