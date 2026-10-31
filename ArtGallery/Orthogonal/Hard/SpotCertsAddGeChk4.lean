module

public import ArtGallery.Orthogonal.Hard.SpotCertsAddGe
public import ArtGallery.Orthogonal.Hard.SpotCertsAddGeHints
public import ArtGallery.Orthogonal.Hard.PropKeysD
public import ArtGallery.Orthogonal.Hard.SpotSplit

/-! # Spot certificate check of the helper `7` of the group `slot addGe` (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gAddGeSC4_head : spotHeadB (slotD .addGe) 7 gAddGeSC4T = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeSC4_base : (gAddGeSC4T.cert (slotD .addGe).gs).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeSC4_p0 : (gAddGeSC4T.cert (slotD .addGe).gs).okPropR 0 50 = true :=
  TCertI.okPropR_of_K gAddGeSC4I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC4H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC4_p50 : (gAddGeSC4T.cert (slotD .addGe).gs).okPropR 50 100 = true :=
  TCertI.okPropR_of_K gAddGeSC4I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC4H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC4_p100 : (gAddGeSC4T.cert (slotD .addGe).gs).okPropR 100 150 = true :=
  TCertI.okPropR_of_K gAddGeSC4I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC4H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC4_p150 : (gAddGeSC4T.cert (slotD .addGe).gs).okPropR 150 200 = true :=
  TCertI.okPropR_of_K gAddGeSC4I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC4H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC4_p200 : (gAddGeSC4T.cert (slotD .addGe).gs).okPropR 200 250 = true :=
  TCertI.okPropR_of_K gAddGeSC4I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC4H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC4_p250 : (gAddGeSC4T.cert (slotD .addGe).gs).okPropR 250 300 = true :=
  TCertI.okPropR_of_K gAddGeSC4I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC4H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC4_p300 : (gAddGeSC4T.cert (slotD .addGe).gs).okPropR 300 350 = true :=
  TCertI.okPropR_of_K gAddGeSC4I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC4H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC4_p350 : (gAddGeSC4T.cert (slotD .addGe).gs).okPropR 350 400 = true :=
  TCertI.okPropR_of_K gAddGeSC4I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC4H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC4_p400 : (gAddGeSC4T.cert (slotD .addGe).gs).okPropR 400 411 = true :=
  TCertI.okPropR_of_K gAddGeSC4I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC4H (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The spot check of the helper `7` of the group `slot addGe`. -/
theorem gAddGeSC4T_ok : spotFarB (slotD .addGe) 7 gAddGeSC4T = true :=
  spotFarB_of_parts gAddGeSC4_head (LCert.ok_of_parts gAddGeSC4_base (n := 411) (by decide +kernel)
    (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) gAddGeSC4_p0 gAddGeSC4_p50) gAddGeSC4_p100) gAddGeSC4_p150) gAddGeSC4_p200) gAddGeSC4_p250) gAddGeSC4_p300) gAddGeSC4_p350) gAddGeSC4_p400))

end

end ArtGallery.Orthogonal.Hard
