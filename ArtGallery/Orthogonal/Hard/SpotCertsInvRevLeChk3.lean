module

public import ArtGallery.Orthogonal.Hard.SpotCertsInvRevLe
public import ArtGallery.Orthogonal.Hard.SpotCertsInvRevLeHints
public import ArtGallery.Orthogonal.Hard.PropKeysD
public import ArtGallery.Orthogonal.Hard.SpotSplit

/-! # Spot certificate check of the helper `5` of the group `slot invRevLe` (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gInvRevLeSC3_head : spotHeadB (slotD .invRevLe) 5 gInvRevLeSC3T = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gInvRevLeSC3_base : (gInvRevLeSC3T.cert (slotD .invRevLe).gs).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gInvRevLeSC3_p0 : (gInvRevLeSC3T.cert (slotD .invRevLe).gs).okPropR 0 50 = true :=
  TCertI.okPropR_of_K gInvRevLeSC3I rfl ((slotD .invRevLe).gs) keysDInvRevLe_ok gInvRevLeSC3H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gInvRevLeSC3_p50 : (gInvRevLeSC3T.cert (slotD .invRevLe).gs).okPropR 50 98 = true :=
  TCertI.okPropR_of_K gInvRevLeSC3I rfl ((slotD .invRevLe).gs) keysDInvRevLe_ok gInvRevLeSC3H (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The spot check of the helper `5` of the group `slot invRevLe`. -/
theorem gInvRevLeSC3T_ok : spotFarB (slotD .invRevLe) 5 gInvRevLeSC3T = true :=
  spotFarB_of_parts gInvRevLeSC3_head (LCert.ok_of_parts gInvRevLeSC3_base (n := 98) (by decide +kernel)
    (allR_join (by norm_num) (by norm_num) gInvRevLeSC3_p0 gInvRevLeSC3_p50))

end

end ArtGallery.Orthogonal.Hard
