module

public import ArtGallery.Orthogonal.Hard.SpotCertsInvGe
public import ArtGallery.Orthogonal.Hard.SpotCertsInvGeHints
public import ArtGallery.Orthogonal.Hard.PropKeysD
public import ArtGallery.Orthogonal.Hard.SpotSplit

/-! # Spot certificate check of the helper `3` of the group `slot invGe` (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gInvGeSC1_head : spotHeadB (slotD .invGe) 3 gInvGeSC1T = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gInvGeSC1_base : (gInvGeSC1T.cert (slotD .invGe).gs).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gInvGeSC1_p0 : (gInvGeSC1T.cert (slotD .invGe).gs).okPropR 0 50 = true :=
  TCertI.okPropR_of_K gInvGeSC1I rfl ((slotD .invGe).gs) keysDInvGe_ok gInvGeSC1H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gInvGeSC1_p50 : (gInvGeSC1T.cert (slotD .invGe).gs).okPropR 50 81 = true :=
  TCertI.okPropR_of_K gInvGeSC1I rfl ((slotD .invGe).gs) keysDInvGe_ok gInvGeSC1H (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The spot check of the helper `3` of the group `slot invGe`. -/
theorem gInvGeSC1T_ok : spotFarB (slotD .invGe) 3 gInvGeSC1T = true :=
  spotFarB_of_parts gInvGeSC1_head (LCert.ok_of_parts gInvGeSC1_base (n := 81) (by decide +kernel)
    (allR_join (by norm_num) (by norm_num) gInvGeSC1_p0 gInvGeSC1_p50))

end

end ArtGallery.Orthogonal.Hard
