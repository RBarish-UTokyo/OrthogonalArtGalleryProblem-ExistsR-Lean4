module

public import ArtGallery.Orthogonal.Hard.SpotCertsAddGe
public import ArtGallery.Orthogonal.Hard.SpotCertsAddGeHints
public import ArtGallery.Orthogonal.Hard.PropKeysD
public import ArtGallery.Orthogonal.Hard.SpotSplit

/-! # Spot certificate check of the helper `12` of the group `slot addGe` (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gAddGeSC9_head : spotHeadB (slotD .addGe) 12 gAddGeSC9T = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeSC9_base : (gAddGeSC9T.cert (slotD .addGe).gs).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeSC9_p0 : (gAddGeSC9T.cert (slotD .addGe).gs).okPropR 0 50 = true :=
  TCertI.okPropR_of_K gAddGeSC9I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC9H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC9_p50 : (gAddGeSC9T.cert (slotD .addGe).gs).okPropR 50 100 = true :=
  TCertI.okPropR_of_K gAddGeSC9I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC9H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC9_p100 : (gAddGeSC9T.cert (slotD .addGe).gs).okPropR 100 150 = true :=
  TCertI.okPropR_of_K gAddGeSC9I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC9H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC9_p150 : (gAddGeSC9T.cert (slotD .addGe).gs).okPropR 150 200 = true :=
  TCertI.okPropR_of_K gAddGeSC9I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC9H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC9_p200 : (gAddGeSC9T.cert (slotD .addGe).gs).okPropR 200 250 = true :=
  TCertI.okPropR_of_K gAddGeSC9I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC9H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC9_p250 : (gAddGeSC9T.cert (slotD .addGe).gs).okPropR 250 300 = true :=
  TCertI.okPropR_of_K gAddGeSC9I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC9H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC9_p300 : (gAddGeSC9T.cert (slotD .addGe).gs).okPropR 300 350 = true :=
  TCertI.okPropR_of_K gAddGeSC9I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC9H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC9_p350 : (gAddGeSC9T.cert (slotD .addGe).gs).okPropR 350 400 = true :=
  TCertI.okPropR_of_K gAddGeSC9I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC9H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC9_p400 : (gAddGeSC9T.cert (slotD .addGe).gs).okPropR 400 411 = true :=
  TCertI.okPropR_of_K gAddGeSC9I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC9H (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The spot check of the helper `12` of the group `slot addGe`. -/
theorem gAddGeSC9T_ok : spotFarB (slotD .addGe) 12 gAddGeSC9T = true :=
  spotFarB_of_parts gAddGeSC9_head (LCert.ok_of_parts gAddGeSC9_base (n := 411) (by decide +kernel)
    (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) gAddGeSC9_p0 gAddGeSC9_p50) gAddGeSC9_p100) gAddGeSC9_p150) gAddGeSC9_p200) gAddGeSC9_p250) gAddGeSC9_p300) gAddGeSC9_p350) gAddGeSC9_p400))

end

end ArtGallery.Orthogonal.Hard
