module

public import ArtGallery.Orthogonal.Hard.SpotCertsAddGe
public import ArtGallery.Orthogonal.Hard.SpotCertsAddGeHints
public import ArtGallery.Orthogonal.Hard.PropKeysD
public import ArtGallery.Orthogonal.Hard.SpotSplit

/-! # Spot certificate check of the helper `13` of the group `slot addGe` (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gAddGeSC10_head : spotHeadB (slotD .addGe) 13 gAddGeSC10T = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeSC10_base : (gAddGeSC10T.cert (slotD .addGe).gs).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeSC10_p0 : (gAddGeSC10T.cert (slotD .addGe).gs).okPropR 0 50 = true :=
  TCertI.okPropR_of_K gAddGeSC10I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC10H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC10_p50 : (gAddGeSC10T.cert (slotD .addGe).gs).okPropR 50 100 = true :=
  TCertI.okPropR_of_K gAddGeSC10I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC10H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC10_p100 : (gAddGeSC10T.cert (slotD .addGe).gs).okPropR 100 150 = true :=
  TCertI.okPropR_of_K gAddGeSC10I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC10H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC10_p150 : (gAddGeSC10T.cert (slotD .addGe).gs).okPropR 150 200 = true :=
  TCertI.okPropR_of_K gAddGeSC10I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC10H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC10_p200 : (gAddGeSC10T.cert (slotD .addGe).gs).okPropR 200 250 = true :=
  TCertI.okPropR_of_K gAddGeSC10I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC10H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC10_p250 : (gAddGeSC10T.cert (slotD .addGe).gs).okPropR 250 300 = true :=
  TCertI.okPropR_of_K gAddGeSC10I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC10H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC10_p300 : (gAddGeSC10T.cert (slotD .addGe).gs).okPropR 300 350 = true :=
  TCertI.okPropR_of_K gAddGeSC10I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC10H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC10_p350 : (gAddGeSC10T.cert (slotD .addGe).gs).okPropR 350 400 = true :=
  TCertI.okPropR_of_K gAddGeSC10I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC10H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC10_p400 : (gAddGeSC10T.cert (slotD .addGe).gs).okPropR 400 411 = true :=
  TCertI.okPropR_of_K gAddGeSC10I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC10H (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The spot check of the helper `13` of the group `slot addGe`. -/
theorem gAddGeSC10T_ok : spotFarB (slotD .addGe) 13 gAddGeSC10T = true :=
  spotFarB_of_parts gAddGeSC10_head (LCert.ok_of_parts gAddGeSC10_base (n := 411) (by decide +kernel)
    (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) gAddGeSC10_p0 gAddGeSC10_p50) gAddGeSC10_p100) gAddGeSC10_p150) gAddGeSC10_p200) gAddGeSC10_p250) gAddGeSC10_p300) gAddGeSC10_p350) gAddGeSC10_p400))

end

end ArtGallery.Orthogonal.Hard
