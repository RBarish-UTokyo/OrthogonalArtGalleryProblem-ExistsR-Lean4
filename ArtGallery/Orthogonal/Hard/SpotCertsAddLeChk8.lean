module

public import ArtGallery.Orthogonal.Hard.SpotCertsAddLe
public import ArtGallery.Orthogonal.Hard.SpotCertsAddLeHints
public import ArtGallery.Orthogonal.Hard.PropKeysD
public import ArtGallery.Orthogonal.Hard.SpotSplit

/-! # Spot certificate check of the helper `11` of the group `slot addLe` (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gAddLeSC8_head : spotHeadB (slotD .addLe) 11 gAddLeSC8T = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeSC8_base : (gAddLeSC8T.cert (slotD .addLe).gs).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeSC8_p0 : (gAddLeSC8T.cert (slotD .addLe).gs).okPropR 0 50 = true :=
  TCertI.okPropR_of_K gAddLeSC8I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC8H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC8_p50 : (gAddLeSC8T.cert (slotD .addLe).gs).okPropR 50 100 = true :=
  TCertI.okPropR_of_K gAddLeSC8I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC8H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC8_p100 : (gAddLeSC8T.cert (slotD .addLe).gs).okPropR 100 150 = true :=
  TCertI.okPropR_of_K gAddLeSC8I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC8H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC8_p150 : (gAddLeSC8T.cert (slotD .addLe).gs).okPropR 150 200 = true :=
  TCertI.okPropR_of_K gAddLeSC8I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC8H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC8_p200 : (gAddLeSC8T.cert (slotD .addLe).gs).okPropR 200 250 = true :=
  TCertI.okPropR_of_K gAddLeSC8I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC8H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC8_p250 : (gAddLeSC8T.cert (slotD .addLe).gs).okPropR 250 300 = true :=
  TCertI.okPropR_of_K gAddLeSC8I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC8H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC8_p300 : (gAddLeSC8T.cert (slotD .addLe).gs).okPropR 300 350 = true :=
  TCertI.okPropR_of_K gAddLeSC8I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC8H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC8_p350 : (gAddLeSC8T.cert (slotD .addLe).gs).okPropR 350 397 = true :=
  TCertI.okPropR_of_K gAddLeSC8I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC8H (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The spot check of the helper `11` of the group `slot addLe`. -/
theorem gAddLeSC8T_ok : spotFarB (slotD .addLe) 11 gAddLeSC8T = true :=
  spotFarB_of_parts gAddLeSC8_head (LCert.ok_of_parts gAddLeSC8_base (n := 397) (by decide +kernel)
    (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) gAddLeSC8_p0 gAddLeSC8_p50) gAddLeSC8_p100) gAddLeSC8_p150) gAddLeSC8_p200) gAddLeSC8_p250) gAddLeSC8_p300) gAddLeSC8_p350))

end

end ArtGallery.Orthogonal.Hard
