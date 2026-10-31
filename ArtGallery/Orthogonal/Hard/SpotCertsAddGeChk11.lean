module

public import ArtGallery.Orthogonal.Hard.SpotCertsAddGe
public import ArtGallery.Orthogonal.Hard.SpotCertsAddGeHints
public import ArtGallery.Orthogonal.Hard.PropKeysD
public import ArtGallery.Orthogonal.Hard.SpotSplit

/-! # Spot certificate check of the helper `14` of the group `slot addGe` (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gAddGeSC11_head : spotHeadB (slotD .addGe) 14 gAddGeSC11T = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeSC11_base : (gAddGeSC11T.cert (slotD .addGe).gs).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeSC11_p0 : (gAddGeSC11T.cert (slotD .addGe).gs).okPropR 0 50 = true :=
  TCertI.okPropR_of_K gAddGeSC11I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC11H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC11_p50 : (gAddGeSC11T.cert (slotD .addGe).gs).okPropR 50 100 = true :=
  TCertI.okPropR_of_K gAddGeSC11I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC11H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC11_p100 : (gAddGeSC11T.cert (slotD .addGe).gs).okPropR 100 150 = true :=
  TCertI.okPropR_of_K gAddGeSC11I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC11H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC11_p150 : (gAddGeSC11T.cert (slotD .addGe).gs).okPropR 150 200 = true :=
  TCertI.okPropR_of_K gAddGeSC11I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC11H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC11_p200 : (gAddGeSC11T.cert (slotD .addGe).gs).okPropR 200 250 = true :=
  TCertI.okPropR_of_K gAddGeSC11I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC11H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC11_p250 : (gAddGeSC11T.cert (slotD .addGe).gs).okPropR 250 300 = true :=
  TCertI.okPropR_of_K gAddGeSC11I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC11H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC11_p300 : (gAddGeSC11T.cert (slotD .addGe).gs).okPropR 300 350 = true :=
  TCertI.okPropR_of_K gAddGeSC11I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC11H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC11_p350 : (gAddGeSC11T.cert (slotD .addGe).gs).okPropR 350 400 = true :=
  TCertI.okPropR_of_K gAddGeSC11I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC11H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeSC11_p400 : (gAddGeSC11T.cert (slotD .addGe).gs).okPropR 400 411 = true :=
  TCertI.okPropR_of_K gAddGeSC11I rfl ((slotD .addGe).gs) keysDAddGe_ok gAddGeSC11H (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The spot check of the helper `14` of the group `slot addGe`. -/
theorem gAddGeSC11T_ok : spotFarB (slotD .addGe) 14 gAddGeSC11T = true :=
  spotFarB_of_parts gAddGeSC11_head (LCert.ok_of_parts gAddGeSC11_base (n := 411) (by decide +kernel)
    (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) gAddGeSC11_p0 gAddGeSC11_p50) gAddGeSC11_p100) gAddGeSC11_p150) gAddGeSC11_p200) gAddGeSC11_p250) gAddGeSC11_p300) gAddGeSC11_p350) gAddGeSC11_p400))

end

end ArtGallery.Orthogonal.Hard
