module

public import ArtGallery.Orthogonal.Hard.SpotCertsInvRevLe
public import ArtGallery.Orthogonal.Hard.SpotCertsInvRevLeHints
public import ArtGallery.Orthogonal.Hard.PropKeysD
public import ArtGallery.Orthogonal.Hard.SpotSplit

/-! # Spot certificate check of the helper `4` of the group `slot invRevLe` (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gInvRevLeSC2_head : spotHeadB (slotD .invRevLe) 4 gInvRevLeSC2T = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gInvRevLeSC2_base : (gInvRevLeSC2T.cert (slotD .invRevLe).gs).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gInvRevLeSC2_p0 : (gInvRevLeSC2T.cert (slotD .invRevLe).gs).okPropR 0 50 = true :=
  TCertI.okPropR_of_K gInvRevLeSC2I rfl ((slotD .invRevLe).gs) keysDInvRevLe_ok gInvRevLeSC2H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gInvRevLeSC2_p50 : (gInvRevLeSC2T.cert (slotD .invRevLe).gs).okPropR 50 98 = true :=
  TCertI.okPropR_of_K gInvRevLeSC2I rfl ((slotD .invRevLe).gs) keysDInvRevLe_ok gInvRevLeSC2H (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The spot check of the helper `4` of the group `slot invRevLe`. -/
theorem gInvRevLeSC2T_ok : spotFarB (slotD .invRevLe) 4 gInvRevLeSC2T = true :=
  spotFarB_of_parts gInvRevLeSC2_head (LCert.ok_of_parts gInvRevLeSC2_base (n := 98) (by decide +kernel)
    (allR_join (by norm_num) (by norm_num) gInvRevLeSC2_p0 gInvRevLeSC2_p50))

end

end ArtGallery.Orthogonal.Hard
