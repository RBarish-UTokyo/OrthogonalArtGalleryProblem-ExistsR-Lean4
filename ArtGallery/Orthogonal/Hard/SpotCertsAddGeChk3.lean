module

public import ArtGallery.Orthogonal.Hard.SpotCertsAddGe
public import ArtGallery.Orthogonal.Hard.SpotCertsAddGeHints
public import ArtGallery.Orthogonal.Hard.PropKeysD
public import ArtGallery.Orthogonal.Hard.SpotSplit

/-! # Spot certificate check of the helper `6` of the group `slot addGe` (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gAddGeSC3_head : spotHeadB (slotD .addGe) 6 gAddGeSC3T = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeSC3_base : (gAddGeSC3T.cert (slotD .addGe).gs).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeSC3_p0 : (gAddGeSC3T.cert (slotD .addGe).gs).okPropR 0 50 = true :=
  TCertI.okPropR_of_K gAddGeSC3I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC3H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC3_p50 : (gAddGeSC3T.cert (slotD .addGe).gs).okPropR 50 100 = true :=
  TCertI.okPropR_of_K gAddGeSC3I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC3H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC3_p100 : (gAddGeSC3T.cert (slotD .addGe).gs).okPropR 100 150 = true :=
  TCertI.okPropR_of_K gAddGeSC3I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC3H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC3_p150 : (gAddGeSC3T.cert (slotD .addGe).gs).okPropR 150 200 = true :=
  TCertI.okPropR_of_K gAddGeSC3I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC3H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC3_p200 : (gAddGeSC3T.cert (slotD .addGe).gs).okPropR 200 250 = true :=
  TCertI.okPropR_of_K gAddGeSC3I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC3H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC3_p250 : (gAddGeSC3T.cert (slotD .addGe).gs).okPropR 250 300 = true :=
  TCertI.okPropR_of_K gAddGeSC3I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC3H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC3_p300 : (gAddGeSC3T.cert (slotD .addGe).gs).okPropR 300 350 = true :=
  TCertI.okPropR_of_K gAddGeSC3I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC3H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC3_p350 : (gAddGeSC3T.cert (slotD .addGe).gs).okPropR 350 400 = true :=
  TCertI.okPropR_of_K gAddGeSC3I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC3H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC3_p400 : (gAddGeSC3T.cert (slotD .addGe).gs).okPropR 400 411 = true :=
  TCertI.okPropR_of_K gAddGeSC3I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC3H (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The spot check of the helper `6` of the group `slot addGe`. -/
theorem gAddGeSC3T_ok : spotFarB (slotD .addGe) 6 gAddGeSC3T = true :=
  spotFarB_of_parts gAddGeSC3_head (LCert.ok_of_parts gAddGeSC3_base (n := 411) (by decide +kernel)
    (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) gAddGeSC3_p0 gAddGeSC3_p50) gAddGeSC3_p100) gAddGeSC3_p150) gAddGeSC3_p200) gAddGeSC3_p250) gAddGeSC3_p300) gAddGeSC3_p350) gAddGeSC3_p400))

end

end ArtGallery.Orthogonal.Hard
