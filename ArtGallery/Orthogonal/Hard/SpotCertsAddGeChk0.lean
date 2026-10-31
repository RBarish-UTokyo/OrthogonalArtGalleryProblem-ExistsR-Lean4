module

public import ArtGallery.Orthogonal.Hard.SpotCertsAddGe
public import ArtGallery.Orthogonal.Hard.SpotCertsAddGeHints
public import ArtGallery.Orthogonal.Hard.PropKeysD
public import ArtGallery.Orthogonal.Hard.SpotSplit

/-! # Spot certificate check of the helper `1` of the group `slot addGe` (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gAddGeSC0_head : spotHeadB (slotD .addGe) 1 gAddGeSC0T = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeSC0_base : (gAddGeSC0T.cert (slotD .addGe).gs).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeSC0_p0 : (gAddGeSC0T.cert (slotD .addGe).gs).okPropR 0 50 = true :=
  TCertI.okPropR_of_K gAddGeSC0I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC0H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC0_p50 : (gAddGeSC0T.cert (slotD .addGe).gs).okPropR 50 100 = true :=
  TCertI.okPropR_of_K gAddGeSC0I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC0H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC0_p100 : (gAddGeSC0T.cert (slotD .addGe).gs).okPropR 100 150 = true :=
  TCertI.okPropR_of_K gAddGeSC0I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC0H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC0_p150 : (gAddGeSC0T.cert (slotD .addGe).gs).okPropR 150 200 = true :=
  TCertI.okPropR_of_K gAddGeSC0I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC0H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC0_p200 : (gAddGeSC0T.cert (slotD .addGe).gs).okPropR 200 250 = true :=
  TCertI.okPropR_of_K gAddGeSC0I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC0H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC0_p250 : (gAddGeSC0T.cert (slotD .addGe).gs).okPropR 250 300 = true :=
  TCertI.okPropR_of_K gAddGeSC0I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC0H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC0_p300 : (gAddGeSC0T.cert (slotD .addGe).gs).okPropR 300 350 = true :=
  TCertI.okPropR_of_K gAddGeSC0I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC0H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC0_p350 : (gAddGeSC0T.cert (slotD .addGe).gs).okPropR 350 400 = true :=
  TCertI.okPropR_of_K gAddGeSC0I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC0H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC0_p400 : (gAddGeSC0T.cert (slotD .addGe).gs).okPropR 400 411 = true :=
  TCertI.okPropR_of_K gAddGeSC0I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC0H (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The spot check of the helper `1` of the group `slot addGe`. -/
theorem gAddGeSC0T_ok : spotFarB (slotD .addGe) 1 gAddGeSC0T = true :=
  spotFarB_of_parts gAddGeSC0_head (LCert.ok_of_parts gAddGeSC0_base (n := 411) (by decide +kernel)
    (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) gAddGeSC0_p0 gAddGeSC0_p50) gAddGeSC0_p100) gAddGeSC0_p150) gAddGeSC0_p200) gAddGeSC0_p250) gAddGeSC0_p300) gAddGeSC0_p350) gAddGeSC0_p400))

end

end ArtGallery.Orthogonal.Hard
