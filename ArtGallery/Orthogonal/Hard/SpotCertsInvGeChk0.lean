module

public import ArtGallery.Orthogonal.Hard.SpotCertsInvGe
public import ArtGallery.Orthogonal.Hard.SpotCertsInvGeHints
public import ArtGallery.Orthogonal.Hard.PropKeysD
public import ArtGallery.Orthogonal.Hard.SpotSplit

/-! # Spot certificate check of the helper `1` of the group `slot invGe` (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gInvGeSC0_head : spotHeadB (slotD .invGe) 1 gInvGeSC0T = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gInvGeSC0_base : (gInvGeSC0T.cert (slotD .invGe).gs).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gInvGeSC0_p0 : (gInvGeSC0T.cert (slotD .invGe).gs).okPropR 0 50 = true :=
  TCertI.okPropR_of_K gInvGeSC0I rfl ((slotD .invGe).gs) keysDInvGe_ok gInvGeSC0H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gInvGeSC0_p50 : (gInvGeSC0T.cert (slotD .invGe).gs).okPropR 50 81 = true :=
  TCertI.okPropR_of_K gInvGeSC0I rfl ((slotD .invGe).gs) keysDInvGe_ok gInvGeSC0H (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The spot check of the helper `1` of the group `slot invGe`. -/
theorem gInvGeSC0T_ok : spotFarB (slotD .invGe) 1 gInvGeSC0T = true :=
  spotFarB_of_parts gInvGeSC0_head (LCert.ok_of_parts gInvGeSC0_base (n := 81) (by decide +kernel)
    (allR_join (by norm_num) (by norm_num) gInvGeSC0_p0 gInvGeSC0_p50))

end

end ArtGallery.Orthogonal.Hard
