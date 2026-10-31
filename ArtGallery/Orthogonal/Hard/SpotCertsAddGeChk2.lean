module

public import ArtGallery.Orthogonal.Hard.SpotCertsAddGe
public import ArtGallery.Orthogonal.Hard.SpotCertsAddGeHints
public import ArtGallery.Orthogonal.Hard.PropKeysD
public import ArtGallery.Orthogonal.Hard.SpotSplit

/-! # Spot certificate check of the helper `5` of the group `slot addGe` (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gAddGeSC2_head : spotHeadB (slotD .addGe) 5 gAddGeSC2T = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeSC2_base : (gAddGeSC2T.cert (slotD .addGe).gs).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeSC2_p0 : (gAddGeSC2T.cert (slotD .addGe).gs).okPropR 0 50 = true :=
  TCertI.okPropR_of_K gAddGeSC2I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC2H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC2_p50 : (gAddGeSC2T.cert (slotD .addGe).gs).okPropR 50 100 = true :=
  TCertI.okPropR_of_K gAddGeSC2I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC2H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC2_p100 : (gAddGeSC2T.cert (slotD .addGe).gs).okPropR 100 150 = true :=
  TCertI.okPropR_of_K gAddGeSC2I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC2H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC2_p150 : (gAddGeSC2T.cert (slotD .addGe).gs).okPropR 150 200 = true :=
  TCertI.okPropR_of_K gAddGeSC2I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC2H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC2_p200 : (gAddGeSC2T.cert (slotD .addGe).gs).okPropR 200 250 = true :=
  TCertI.okPropR_of_K gAddGeSC2I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC2H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC2_p250 : (gAddGeSC2T.cert (slotD .addGe).gs).okPropR 250 300 = true :=
  TCertI.okPropR_of_K gAddGeSC2I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC2H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC2_p300 : (gAddGeSC2T.cert (slotD .addGe).gs).okPropR 300 350 = true :=
  TCertI.okPropR_of_K gAddGeSC2I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC2H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC2_p350 : (gAddGeSC2T.cert (slotD .addGe).gs).okPropR 350 400 = true :=
  TCertI.okPropR_of_K gAddGeSC2I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC2H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC2_p400 : (gAddGeSC2T.cert (slotD .addGe).gs).okPropR 400 411 = true :=
  TCertI.okPropR_of_K gAddGeSC2I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC2H (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The spot check of the helper `5` of the group `slot addGe`. -/
theorem gAddGeSC2T_ok : spotFarB (slotD .addGe) 5 gAddGeSC2T = true :=
  spotFarB_of_parts gAddGeSC2_head (LCert.ok_of_parts gAddGeSC2_base (n := 411) (by decide +kernel)
    (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) gAddGeSC2_p0 gAddGeSC2_p50) gAddGeSC2_p100) gAddGeSC2_p150) gAddGeSC2_p200) gAddGeSC2_p250) gAddGeSC2_p300) gAddGeSC2_p350) gAddGeSC2_p400))

end

end ArtGallery.Orthogonal.Hard
