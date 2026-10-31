module

public import ArtGallery.Orthogonal.Hard.SpotCertsAddLe
public import ArtGallery.Orthogonal.Hard.SpotCertsAddLeHints
public import ArtGallery.Orthogonal.Hard.PropKeysD
public import ArtGallery.Orthogonal.Hard.SpotSplit

/-! # Spot certificate check of the helper `5` of the group `slot addLe` (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gAddLeSC2_head : spotHeadB (slotD .addLe) 5 gAddLeSC2T = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeSC2_base : (gAddLeSC2T.cert (slotD .addLe).gs).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeSC2_p0 : (gAddLeSC2T.cert (slotD .addLe).gs).okPropR 0 50 = true :=
  TCertI.okPropR_of_K gAddLeSC2I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC2H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC2_p50 : (gAddLeSC2T.cert (slotD .addLe).gs).okPropR 50 100 = true :=
  TCertI.okPropR_of_K gAddLeSC2I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC2H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC2_p100 : (gAddLeSC2T.cert (slotD .addLe).gs).okPropR 100 150 = true :=
  TCertI.okPropR_of_K gAddLeSC2I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC2H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC2_p150 : (gAddLeSC2T.cert (slotD .addLe).gs).okPropR 150 200 = true :=
  TCertI.okPropR_of_K gAddLeSC2I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC2H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC2_p200 : (gAddLeSC2T.cert (slotD .addLe).gs).okPropR 200 250 = true :=
  TCertI.okPropR_of_K gAddLeSC2I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC2H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC2_p250 : (gAddLeSC2T.cert (slotD .addLe).gs).okPropR 250 300 = true :=
  TCertI.okPropR_of_K gAddLeSC2I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC2H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC2_p300 : (gAddLeSC2T.cert (slotD .addLe).gs).okPropR 300 350 = true :=
  TCertI.okPropR_of_K gAddLeSC2I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC2H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC2_p350 : (gAddLeSC2T.cert (slotD .addLe).gs).okPropR 350 397 = true :=
  TCertI.okPropR_of_K gAddLeSC2I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC2H (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The spot check of the helper `5` of the group `slot addLe`. -/
theorem gAddLeSC2T_ok : spotFarB (slotD .addLe) 5 gAddLeSC2T = true :=
  spotFarB_of_parts gAddLeSC2_head (LCert.ok_of_parts gAddLeSC2_base (n := 397) (by decide +kernel)
    (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) gAddLeSC2_p0 gAddLeSC2_p50) gAddLeSC2_p100) gAddLeSC2_p150) gAddLeSC2_p200) gAddLeSC2_p250) gAddLeSC2_p300) gAddLeSC2_p350))

end

end ArtGallery.Orthogonal.Hard
