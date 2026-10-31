module

public import ArtGallery.Orthogonal.Hard.SpotCertsAddLe
public import ArtGallery.Orthogonal.Hard.SpotCertsAddLeHints
public import ArtGallery.Orthogonal.Hard.PropKeysD
public import ArtGallery.Orthogonal.Hard.SpotSplit

/-! # Spot certificate check of the helper `10` of the group `slot addLe` (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gAddLeSC7_head : spotHeadB (slotD .addLe) 10 gAddLeSC7T = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeSC7_base : (gAddLeSC7T.cert (slotD .addLe).gs).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeSC7_p0 : (gAddLeSC7T.cert (slotD .addLe).gs).okPropR 0 50 = true :=
  TCertI.okPropR_of_K gAddLeSC7I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC7H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC7_p50 : (gAddLeSC7T.cert (slotD .addLe).gs).okPropR 50 100 = true :=
  TCertI.okPropR_of_K gAddLeSC7I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC7H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC7_p100 : (gAddLeSC7T.cert (slotD .addLe).gs).okPropR 100 150 = true :=
  TCertI.okPropR_of_K gAddLeSC7I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC7H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC7_p150 : (gAddLeSC7T.cert (slotD .addLe).gs).okPropR 150 200 = true :=
  TCertI.okPropR_of_K gAddLeSC7I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC7H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC7_p200 : (gAddLeSC7T.cert (slotD .addLe).gs).okPropR 200 250 = true :=
  TCertI.okPropR_of_K gAddLeSC7I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC7H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC7_p250 : (gAddLeSC7T.cert (slotD .addLe).gs).okPropR 250 300 = true :=
  TCertI.okPropR_of_K gAddLeSC7I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC7H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC7_p300 : (gAddLeSC7T.cert (slotD .addLe).gs).okPropR 300 350 = true :=
  TCertI.okPropR_of_K gAddLeSC7I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC7H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC7_p350 : (gAddLeSC7T.cert (slotD .addLe).gs).okPropR 350 397 = true :=
  TCertI.okPropR_of_K gAddLeSC7I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC7H (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The spot check of the helper `10` of the group `slot addLe`. -/
theorem gAddLeSC7T_ok : spotFarB (slotD .addLe) 10 gAddLeSC7T = true :=
  spotFarB_of_parts gAddLeSC7_head (LCert.ok_of_parts gAddLeSC7_base (n := 397) (by decide +kernel)
    (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) gAddLeSC7_p0 gAddLeSC7_p50) gAddLeSC7_p100) gAddLeSC7_p150) gAddLeSC7_p200) gAddLeSC7_p250) gAddLeSC7_p300) gAddLeSC7_p350))

end

end ArtGallery.Orthogonal.Hard
