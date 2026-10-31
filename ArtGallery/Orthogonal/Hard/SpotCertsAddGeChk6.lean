module

public import ArtGallery.Orthogonal.Hard.SpotCertsAddGe
public import ArtGallery.Orthogonal.Hard.SpotCertsAddGeHints
public import ArtGallery.Orthogonal.Hard.PropKeysD
public import ArtGallery.Orthogonal.Hard.SpotSplit

/-! # Spot certificate check of the helper `9` of the group `slot addGe` (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gAddGeSC6_head : spotHeadB (slotD .addGe) 9 gAddGeSC6T = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeSC6_base : (gAddGeSC6T.cert (slotD .addGe).gs).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeSC6_p0 : (gAddGeSC6T.cert (slotD .addGe).gs).okPropR 0 50 = true :=
  TCertI.okPropR_of_K gAddGeSC6I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC6H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC6_p50 : (gAddGeSC6T.cert (slotD .addGe).gs).okPropR 50 100 = true :=
  TCertI.okPropR_of_K gAddGeSC6I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC6H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC6_p100 : (gAddGeSC6T.cert (slotD .addGe).gs).okPropR 100 150 = true :=
  TCertI.okPropR_of_K gAddGeSC6I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC6H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC6_p150 : (gAddGeSC6T.cert (slotD .addGe).gs).okPropR 150 200 = true :=
  TCertI.okPropR_of_K gAddGeSC6I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC6H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC6_p200 : (gAddGeSC6T.cert (slotD .addGe).gs).okPropR 200 250 = true :=
  TCertI.okPropR_of_K gAddGeSC6I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC6H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC6_p250 : (gAddGeSC6T.cert (slotD .addGe).gs).okPropR 250 300 = true :=
  TCertI.okPropR_of_K gAddGeSC6I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC6H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC6_p300 : (gAddGeSC6T.cert (slotD .addGe).gs).okPropR 300 350 = true :=
  TCertI.okPropR_of_K gAddGeSC6I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC6H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC6_p350 : (gAddGeSC6T.cert (slotD .addGe).gs).okPropR 350 400 = true :=
  TCertI.okPropR_of_K gAddGeSC6I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC6H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC6_p400 : (gAddGeSC6T.cert (slotD .addGe).gs).okPropR 400 411 = true :=
  TCertI.okPropR_of_K gAddGeSC6I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC6H (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The spot check of the helper `9` of the group `slot addGe`. -/
theorem gAddGeSC6T_ok : spotFarB (slotD .addGe) 9 gAddGeSC6T = true :=
  spotFarB_of_parts gAddGeSC6_head (LCert.ok_of_parts gAddGeSC6_base (n := 411) (by decide +kernel)
    (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) gAddGeSC6_p0 gAddGeSC6_p50) gAddGeSC6_p100) gAddGeSC6_p150) gAddGeSC6_p200) gAddGeSC6_p250) gAddGeSC6_p300) gAddGeSC6_p350) gAddGeSC6_p400))

end

end ArtGallery.Orthogonal.Hard
