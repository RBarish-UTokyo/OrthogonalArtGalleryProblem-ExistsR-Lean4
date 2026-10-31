module

public import ArtGallery.Orthogonal.Hard.SpotCertsInvGe
public import ArtGallery.Orthogonal.Hard.SpotCertsInvGeHints
public import ArtGallery.Orthogonal.Hard.PropKeysD
public import ArtGallery.Orthogonal.Hard.SpotSplit

/-! # Spot certificate check of the helper `4` of the group `slot invGe` (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gInvGeSC2_head : spotHeadB (slotD .invGe) 4 gInvGeSC2T = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gInvGeSC2_base : (gInvGeSC2T.cert (slotD .invGe).gs).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gInvGeSC2_p0 : (gInvGeSC2T.cert (slotD .invGe).gs).okPropR 0 50 = true :=
  TCertI.okPropR_of_K gInvGeSC2I rfl ((slotD .invGe).gs) keysDInvGe_ok gInvGeSC2H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gInvGeSC2_p50 : (gInvGeSC2T.cert (slotD .invGe).gs).okPropR 50 81 = true :=
  TCertI.okPropR_of_K gInvGeSC2I rfl ((slotD .invGe).gs) keysDInvGe_ok gInvGeSC2H (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The spot check of the helper `4` of the group `slot invGe`. -/
theorem gInvGeSC2T_ok : spotFarB (slotD .invGe) 4 gInvGeSC2T = true :=
  spotFarB_of_parts gInvGeSC2_head (LCert.ok_of_parts gInvGeSC2_base (n := 81) (by decide +kernel)
    (allR_join (by norm_num) (by norm_num) gInvGeSC2_p0 gInvGeSC2_p50))

end

end ArtGallery.Orthogonal.Hard
