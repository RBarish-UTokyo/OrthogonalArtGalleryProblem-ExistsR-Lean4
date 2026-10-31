module

public import ArtGallery.Orthogonal.Hard.SpotCertsAddLe
public import ArtGallery.Orthogonal.Hard.SpotCertsAddLeHints
public import ArtGallery.Orthogonal.Hard.PropKeysD
public import ArtGallery.Orthogonal.Hard.SpotSplit

/-! # Spot certificate check of the helper `13` of the group `slot addLe` (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gAddLeSC10_head : spotHeadB (slotD .addLe) 13 gAddLeSC10T = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeSC10_base : (gAddLeSC10T.cert (slotD .addLe).gs).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeSC10_p0 : (gAddLeSC10T.cert (slotD .addLe).gs).okPropR 0 50 = true :=
  TCertI.okPropR_of_K gAddLeSC10I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC10H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC10_p50 : (gAddLeSC10T.cert (slotD .addLe).gs).okPropR 50 100 = true :=
  TCertI.okPropR_of_K gAddLeSC10I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC10H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC10_p100 : (gAddLeSC10T.cert (slotD .addLe).gs).okPropR 100 150 = true :=
  TCertI.okPropR_of_K gAddLeSC10I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC10H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC10_p150 : (gAddLeSC10T.cert (slotD .addLe).gs).okPropR 150 200 = true :=
  TCertI.okPropR_of_K gAddLeSC10I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC10H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC10_p200 : (gAddLeSC10T.cert (slotD .addLe).gs).okPropR 200 250 = true :=
  TCertI.okPropR_of_K gAddLeSC10I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC10H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC10_p250 : (gAddLeSC10T.cert (slotD .addLe).gs).okPropR 250 300 = true :=
  TCertI.okPropR_of_K gAddLeSC10I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC10H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC10_p300 : (gAddLeSC10T.cert (slotD .addLe).gs).okPropR 300 350 = true :=
  TCertI.okPropR_of_K gAddLeSC10I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC10H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC10_p350 : (gAddLeSC10T.cert (slotD .addLe).gs).okPropR 350 397 = true :=
  TCertI.okPropR_of_K gAddLeSC10I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC10H (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The spot check of the helper `13` of the group `slot addLe`. -/
theorem gAddLeSC10T_ok : spotFarB (slotD .addLe) 13 gAddLeSC10T = true :=
  spotFarB_of_parts gAddLeSC10_head (LCert.ok_of_parts gAddLeSC10_base (n := 397) (by decide +kernel)
    (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) gAddLeSC10_p0 gAddLeSC10_p50) gAddLeSC10_p100) gAddLeSC10_p150) gAddLeSC10_p200) gAddLeSC10_p250) gAddLeSC10_p300) gAddLeSC10_p350))

end

end ArtGallery.Orthogonal.Hard
