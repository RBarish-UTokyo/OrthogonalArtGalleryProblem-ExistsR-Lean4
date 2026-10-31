module

public import ArtGallery.Orthogonal.Hard.PinsInvGe

/-!
# Pin checks of the group `slot invGe`, part 3 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gInvGeHQ_ok : gInvGeHQ.all (hqB (slotZ .invGe) gInvGeWs gInvGePs gInvGeSps) = true := by decide +kernel

end

end ArtGallery.Orthogonal.Hard
