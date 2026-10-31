module

public import ArtGallery.Orthogonal.Hard.SpotCertsAddLe
public import ArtGallery.Orthogonal.Hard.SpotCertsAddLeHints
public import ArtGallery.Orthogonal.Hard.PropKeysD
public import ArtGallery.Orthogonal.Hard.SpotSplit

/-! # Spot certificate check of the helper `7` of the group `slot addLe` (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gAddLeSC4_head : spotHeadB (slotD .addLe) 7 gAddLeSC4T = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeSC4_base : (gAddLeSC4T.cert (slotD .addLe).gs).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeSC4_p0 : (gAddLeSC4T.cert (slotD .addLe).gs).okPropR 0 50 = true :=
  TCertI.okPropR_of_K gAddLeSC4I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC4H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC4_p50 : (gAddLeSC4T.cert (slotD .addLe).gs).okPropR 50 100 = true :=
  TCertI.okPropR_of_K gAddLeSC4I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC4H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC4_p100 : (gAddLeSC4T.cert (slotD .addLe).gs).okPropR 100 150 = true :=
  TCertI.okPropR_of_K gAddLeSC4I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC4H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC4_p150 : (gAddLeSC4T.cert (slotD .addLe).gs).okPropR 150 200 = true :=
  TCertI.okPropR_of_K gAddLeSC4I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC4H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC4_p200 : (gAddLeSC4T.cert (slotD .addLe).gs).okPropR 200 250 = true :=
  TCertI.okPropR_of_K gAddLeSC4I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC4H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC4_p250 : (gAddLeSC4T.cert (slotD .addLe).gs).okPropR 250 300 = true :=
  TCertI.okPropR_of_K gAddLeSC4I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC4H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC4_p300 : (gAddLeSC4T.cert (slotD .addLe).gs).okPropR 300 350 = true :=
  TCertI.okPropR_of_K gAddLeSC4I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC4H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC4_p350 : (gAddLeSC4T.cert (slotD .addLe).gs).okPropR 350 397 = true :=
  TCertI.okPropR_of_K gAddLeSC4I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC4H (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The spot check of the helper `7` of the group `slot addLe`. -/
theorem gAddLeSC4T_ok : spotFarB (slotD .addLe) 7 gAddLeSC4T = true :=
  spotFarB_of_parts gAddLeSC4_head (LCert.ok_of_parts gAddLeSC4_base (n := 397) (by decide +kernel)
    (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) gAddLeSC4_p0 gAddLeSC4_p50) gAddLeSC4_p100) gAddLeSC4_p150) gAddLeSC4_p200) gAddLeSC4_p250) gAddLeSC4_p300) gAddLeSC4_p350))

end

end ArtGallery.Orthogonal.Hard
