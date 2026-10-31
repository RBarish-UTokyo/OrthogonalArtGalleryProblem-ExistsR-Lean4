module

public import ArtGallery.Orthogonal.Hard.SpotCertsAddLe
public import ArtGallery.Orthogonal.Hard.SpotCertsAddLeHints
public import ArtGallery.Orthogonal.Hard.PropKeysD
public import ArtGallery.Orthogonal.Hard.SpotSplit

/-! # Spot certificate check of the helper `9` of the group `slot addLe` (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gAddLeSC6_head : spotHeadB (slotD .addLe) 9 gAddLeSC6T = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeSC6_base : (gAddLeSC6T.cert (slotD .addLe).gs).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeSC6_p0 : (gAddLeSC6T.cert (slotD .addLe).gs).okPropR 0 50 = true :=
  TCertI.okPropR_of_K gAddLeSC6I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC6H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC6_p50 : (gAddLeSC6T.cert (slotD .addLe).gs).okPropR 50 100 = true :=
  TCertI.okPropR_of_K gAddLeSC6I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC6H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC6_p100 : (gAddLeSC6T.cert (slotD .addLe).gs).okPropR 100 150 = true :=
  TCertI.okPropR_of_K gAddLeSC6I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC6H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC6_p150 : (gAddLeSC6T.cert (slotD .addLe).gs).okPropR 150 200 = true :=
  TCertI.okPropR_of_K gAddLeSC6I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC6H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC6_p200 : (gAddLeSC6T.cert (slotD .addLe).gs).okPropR 200 250 = true :=
  TCertI.okPropR_of_K gAddLeSC6I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC6H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC6_p250 : (gAddLeSC6T.cert (slotD .addLe).gs).okPropR 250 300 = true :=
  TCertI.okPropR_of_K gAddLeSC6I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC6H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC6_p300 : (gAddLeSC6T.cert (slotD .addLe).gs).okPropR 300 350 = true :=
  TCertI.okPropR_of_K gAddLeSC6I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC6H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC6_p350 : (gAddLeSC6T.cert (slotD .addLe).gs).okPropR 350 397 = true :=
  TCertI.okPropR_of_K gAddLeSC6I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC6H (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The spot check of the helper `9` of the group `slot addLe`. -/
theorem gAddLeSC6T_ok : spotFarB (slotD .addLe) 9 gAddLeSC6T = true :=
  spotFarB_of_parts gAddLeSC6_head (LCert.ok_of_parts gAddLeSC6_base (n := 397) (by decide +kernel)
    (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) gAddLeSC6_p0 gAddLeSC6_p50) gAddLeSC6_p100) gAddLeSC6_p150) gAddLeSC6_p200) gAddLeSC6_p250) gAddLeSC6_p300) gAddLeSC6_p350))

end

end ArtGallery.Orthogonal.Hard
