module

public import ArtGallery.Orthogonal.Hard.SpotCertsInvRevLe
public import ArtGallery.Orthogonal.Hard.SpotCertsInvRevLeHints
public import ArtGallery.Orthogonal.Hard.PropKeysD
public import ArtGallery.Orthogonal.Hard.SpotSplit

/-! # Spot certificate check of the helper `6` of the group `slot invRevLe` (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gInvRevLeSC4_head : spotHeadB (slotD .invRevLe) 6 gInvRevLeSC4T = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gInvRevLeSC4_base : (gInvRevLeSC4T.cert (slotD .invRevLe).gs).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gInvRevLeSC4_p0 : (gInvRevLeSC4T.cert (slotD .invRevLe).gs).okPropR 0 50 = true :=
  TCertI.okPropR_of_K gInvRevLeSC4I rfl ((slotD .invRevLe).gs) keysDInvRevLe_ok gInvRevLeSC4H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gInvRevLeSC4_p50 : (gInvRevLeSC4T.cert (slotD .invRevLe).gs).okPropR 50 98 = true :=
  TCertI.okPropR_of_K gInvRevLeSC4I rfl ((slotD .invRevLe).gs) keysDInvRevLe_ok gInvRevLeSC4H (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The spot check of the helper `6` of the group `slot invRevLe`. -/
theorem gInvRevLeSC4T_ok : spotFarB (slotD .invRevLe) 6 gInvRevLeSC4T = true :=
  spotFarB_of_parts gInvRevLeSC4_head (LCert.ok_of_parts gInvRevLeSC4_base (n := 98) (by decide +kernel)
    (allR_join (by norm_num) (by norm_num) gInvRevLeSC4_p0 gInvRevLeSC4_p50))

end

end ArtGallery.Orthogonal.Hard
