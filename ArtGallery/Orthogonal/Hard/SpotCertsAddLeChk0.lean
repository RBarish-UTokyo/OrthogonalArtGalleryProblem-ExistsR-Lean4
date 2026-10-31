module

public import ArtGallery.Orthogonal.Hard.SpotCertsAddLe
public import ArtGallery.Orthogonal.Hard.SpotCertsAddLeHints
public import ArtGallery.Orthogonal.Hard.PropKeysD
public import ArtGallery.Orthogonal.Hard.SpotSplit

/-! # Spot certificate check of the helper `1` of the group `slot addLe` (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gAddLeSC0_head : spotHeadB (slotD .addLe) 1 gAddLeSC0T = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeSC0_base : (gAddLeSC0T.cert (slotD .addLe).gs).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeSC0_p0 : (gAddLeSC0T.cert (slotD .addLe).gs).okPropR 0 50 = true :=
  TCertI.okPropR_of_K gAddLeSC0I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC0H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC0_p50 : (gAddLeSC0T.cert (slotD .addLe).gs).okPropR 50 100 = true :=
  TCertI.okPropR_of_K gAddLeSC0I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC0H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC0_p100 : (gAddLeSC0T.cert (slotD .addLe).gs).okPropR 100 150 = true :=
  TCertI.okPropR_of_K gAddLeSC0I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC0H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC0_p150 : (gAddLeSC0T.cert (slotD .addLe).gs).okPropR 150 200 = true :=
  TCertI.okPropR_of_K gAddLeSC0I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC0H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC0_p200 : (gAddLeSC0T.cert (slotD .addLe).gs).okPropR 200 250 = true :=
  TCertI.okPropR_of_K gAddLeSC0I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC0H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC0_p250 : (gAddLeSC0T.cert (slotD .addLe).gs).okPropR 250 300 = true :=
  TCertI.okPropR_of_K gAddLeSC0I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC0H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC0_p300 : (gAddLeSC0T.cert (slotD .addLe).gs).okPropR 300 350 = true :=
  TCertI.okPropR_of_K gAddLeSC0I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC0H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC0_p350 : (gAddLeSC0T.cert (slotD .addLe).gs).okPropR 350 397 = true :=
  TCertI.okPropR_of_K gAddLeSC0I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC0H (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The spot check of the helper `1` of the group `slot addLe`. -/
theorem gAddLeSC0T_ok : spotFarB (slotD .addLe) 1 gAddLeSC0T = true :=
  spotFarB_of_parts gAddLeSC0_head (LCert.ok_of_parts gAddLeSC0_base (n := 397) (by decide +kernel)
    (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) gAddLeSC0_p0 gAddLeSC0_p50) gAddLeSC0_p100) gAddLeSC0_p150) gAddLeSC0_p200) gAddLeSC0_p250) gAddLeSC0_p300) gAddLeSC0_p350))

end

end ArtGallery.Orthogonal.Hard
