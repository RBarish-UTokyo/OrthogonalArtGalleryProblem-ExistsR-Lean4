module

public import ArtGallery.Orthogonal.Hard.SpotCertsAddLe
public import ArtGallery.Orthogonal.Hard.SpotCertsAddLeHints
public import ArtGallery.Orthogonal.Hard.PropKeysD
public import ArtGallery.Orthogonal.Hard.SpotSplit

/-! # Spot certificate check of the helper `12` of the group `slot addLe` (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gAddLeSC9_head : spotHeadB (slotD .addLe) 12 gAddLeSC9T = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeSC9_base : (gAddLeSC9T.cert (slotD .addLe).gs).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeSC9_p0 : (gAddLeSC9T.cert (slotD .addLe).gs).okPropR 0 50 = true :=
  TCertI.okPropR_of_K gAddLeSC9I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC9H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC9_p50 : (gAddLeSC9T.cert (slotD .addLe).gs).okPropR 50 100 = true :=
  TCertI.okPropR_of_K gAddLeSC9I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC9H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC9_p100 : (gAddLeSC9T.cert (slotD .addLe).gs).okPropR 100 150 = true :=
  TCertI.okPropR_of_K gAddLeSC9I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC9H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC9_p150 : (gAddLeSC9T.cert (slotD .addLe).gs).okPropR 150 200 = true :=
  TCertI.okPropR_of_K gAddLeSC9I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC9H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC9_p200 : (gAddLeSC9T.cert (slotD .addLe).gs).okPropR 200 250 = true :=
  TCertI.okPropR_of_K gAddLeSC9I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC9H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC9_p250 : (gAddLeSC9T.cert (slotD .addLe).gs).okPropR 250 300 = true :=
  TCertI.okPropR_of_K gAddLeSC9I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC9H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC9_p300 : (gAddLeSC9T.cert (slotD .addLe).gs).okPropR 300 350 = true :=
  TCertI.okPropR_of_K gAddLeSC9I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC9H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeSC9_p350 : (gAddLeSC9T.cert (slotD .addLe).gs).okPropR 350 397 = true :=
  TCertI.okPropR_of_K gAddLeSC9I rfl ((slotD .addLe).gs) keysDAddLe_ok gAddLeSC9H (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The spot check of the helper `12` of the group `slot addLe`. -/
theorem gAddLeSC9T_ok : spotFarB (slotD .addLe) 12 gAddLeSC9T = true :=
  spotFarB_of_parts gAddLeSC9_head (LCert.ok_of_parts gAddLeSC9_base (n := 397) (by decide +kernel)
    (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) gAddLeSC9_p0 gAddLeSC9_p50) gAddLeSC9_p100) gAddLeSC9_p150) gAddLeSC9_p200) gAddLeSC9_p250) gAddLeSC9_p300) gAddLeSC9_p350))

end

end ArtGallery.Orthogonal.Hard
