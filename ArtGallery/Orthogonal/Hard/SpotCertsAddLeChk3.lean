module

public import ArtGallery.Orthogonal.Hard.SpotCertsAddLe
public import ArtGallery.Orthogonal.Hard.SpotCertsAddLeHints
public import ArtGallery.Orthogonal.Hard.PropKeysD
public import ArtGallery.Orthogonal.Hard.SpotSplit

/-! # Spot certificate check of the helper `6` of the group `slot addLe` (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gAddLeSC3_head : spotHeadB (slotD .addLe) 6 gAddLeSC3T = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeSC3_base : (gAddLeSC3T.cert (slotD .addLe).gs).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeSC3_p0 : (gAddLeSC3T.cert (slotD .addLe).gs).okPropR 0 50 = true :=
  TCertI.okPropR_of_K gAddLeSC3I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC3H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC3_p50 : (gAddLeSC3T.cert (slotD .addLe).gs).okPropR 50 100 = true :=
  TCertI.okPropR_of_K gAddLeSC3I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC3H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC3_p100 : (gAddLeSC3T.cert (slotD .addLe).gs).okPropR 100 150 = true :=
  TCertI.okPropR_of_K gAddLeSC3I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC3H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC3_p150 : (gAddLeSC3T.cert (slotD .addLe).gs).okPropR 150 200 = true :=
  TCertI.okPropR_of_K gAddLeSC3I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC3H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC3_p200 : (gAddLeSC3T.cert (slotD .addLe).gs).okPropR 200 250 = true :=
  TCertI.okPropR_of_K gAddLeSC3I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC3H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC3_p250 : (gAddLeSC3T.cert (slotD .addLe).gs).okPropR 250 300 = true :=
  TCertI.okPropR_of_K gAddLeSC3I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC3H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC3_p300 : (gAddLeSC3T.cert (slotD .addLe).gs).okPropR 300 350 = true :=
  TCertI.okPropR_of_K gAddLeSC3I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC3H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC3_p350 : (gAddLeSC3T.cert (slotD .addLe).gs).okPropR 350 397 = true :=
  TCertI.okPropR_of_K gAddLeSC3I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC3H (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The spot check of the helper `6` of the group `slot addLe`. -/
theorem gAddLeSC3T_ok : spotFarB (slotD .addLe) 6 gAddLeSC3T = true :=
  spotFarB_of_parts gAddLeSC3_head (LCert.ok_of_parts gAddLeSC3_base (n := 397) (by decide +kernel)
    (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) gAddLeSC3_p0 gAddLeSC3_p50) gAddLeSC3_p100) gAddLeSC3_p150) gAddLeSC3_p200) gAddLeSC3_p250) gAddLeSC3_p300) gAddLeSC3_p350))

end

end ArtGallery.Orthogonal.Hard
