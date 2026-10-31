module

public import ArtGallery.Orthogonal.Hard.SpotCertsInvGe
public import ArtGallery.Orthogonal.Hard.SpotCertsInvGeHints
public import ArtGallery.Orthogonal.Hard.PropKeysD
public import ArtGallery.Orthogonal.Hard.SpotSplit

/-! # Spot certificate check of the helper `5` of the group `slot invGe` (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gInvGeSC3_head : spotHeadB (slotD .invGe) 5 gInvGeSC3T = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gInvGeSC3_base : (gInvGeSC3T.cert (slotD .invGe).gs).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gInvGeSC3_p0 : (gInvGeSC3T.cert (slotD .invGe).gs).okPropR 0 50 = true :=
  TCertI.okPropR_of_K gInvGeSC3I rfl ((slotD .invGe).gs) keysDInvGe_ok gInvGeSC3H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gInvGeSC3_p50 : (gInvGeSC3T.cert (slotD .invGe).gs).okPropR 50 81 = true :=
  TCertI.okPropR_of_K gInvGeSC3I rfl ((slotD .invGe).gs) keysDInvGe_ok gInvGeSC3H (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The spot check of the helper `5` of the group `slot invGe`. -/
theorem gInvGeSC3T_ok : spotFarB (slotD .invGe) 5 gInvGeSC3T = true :=
  spotFarB_of_parts gInvGeSC3_head (LCert.ok_of_parts gInvGeSC3_base (n := 81) (by decide +kernel)
    (allR_join (by norm_num) (by norm_num) gInvGeSC3_p0 gInvGeSC3_p50))

end

end ArtGallery.Orthogonal.Hard
