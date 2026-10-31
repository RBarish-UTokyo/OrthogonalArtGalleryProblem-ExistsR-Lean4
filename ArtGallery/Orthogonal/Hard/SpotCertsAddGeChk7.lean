module

public import ArtGallery.Orthogonal.Hard.SpotCertsAddGe
public import ArtGallery.Orthogonal.Hard.SpotCertsAddGeHints
public import ArtGallery.Orthogonal.Hard.PropKeysD
public import ArtGallery.Orthogonal.Hard.SpotSplit

/-! # Spot certificate check of the helper `10` of the group `slot addGe` (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gAddGeSC7_head : spotHeadB (slotD .addGe) 10 gAddGeSC7T = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeSC7_base : (gAddGeSC7T.cert (slotD .addGe).gs).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeSC7_p0 : (gAddGeSC7T.cert (slotD .addGe).gs).okPropR 0 50 = true :=
  TCertI.okPropR_of_K gAddGeSC7I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC7H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC7_p50 : (gAddGeSC7T.cert (slotD .addGe).gs).okPropR 50 100 = true :=
  TCertI.okPropR_of_K gAddGeSC7I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC7H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC7_p100 : (gAddGeSC7T.cert (slotD .addGe).gs).okPropR 100 150 = true :=
  TCertI.okPropR_of_K gAddGeSC7I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC7H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC7_p150 : (gAddGeSC7T.cert (slotD .addGe).gs).okPropR 150 200 = true :=
  TCertI.okPropR_of_K gAddGeSC7I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC7H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC7_p200 : (gAddGeSC7T.cert (slotD .addGe).gs).okPropR 200 250 = true :=
  TCertI.okPropR_of_K gAddGeSC7I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC7H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC7_p250 : (gAddGeSC7T.cert (slotD .addGe).gs).okPropR 250 300 = true :=
  TCertI.okPropR_of_K gAddGeSC7I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC7H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC7_p300 : (gAddGeSC7T.cert (slotD .addGe).gs).okPropR 300 350 = true :=
  TCertI.okPropR_of_K gAddGeSC7I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC7H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC7_p350 : (gAddGeSC7T.cert (slotD .addGe).gs).okPropR 350 400 = true :=
  TCertI.okPropR_of_K gAddGeSC7I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC7H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC7_p400 : (gAddGeSC7T.cert (slotD .addGe).gs).okPropR 400 411 = true :=
  TCertI.okPropR_of_K gAddGeSC7I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC7H (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The spot check of the helper `10` of the group `slot addGe`. -/
theorem gAddGeSC7T_ok : spotFarB (slotD .addGe) 10 gAddGeSC7T = true :=
  spotFarB_of_parts gAddGeSC7_head (LCert.ok_of_parts gAddGeSC7_base (n := 411) (by decide +kernel)
    (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) gAddGeSC7_p0 gAddGeSC7_p50) gAddGeSC7_p100) gAddGeSC7_p150) gAddGeSC7_p200) gAddGeSC7_p250) gAddGeSC7_p300) gAddGeSC7_p350) gAddGeSC7_p400))

end

end ArtGallery.Orthogonal.Hard
