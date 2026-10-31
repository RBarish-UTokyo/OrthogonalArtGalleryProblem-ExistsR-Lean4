module

public import ArtGallery.Orthogonal.Hard.PinsAddLe
public import ArtGallery.Orthogonal.Hard.PinSplit

/-!
# Pin checks of the group `slot addLe`, part 23 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gAddLeHQ_ok : gAddLeHQ.all (hqB (slotZ .addLe) gAddLeWs gAddLePs gAddLeSps) = true := by decide +kernel

end

end ArtGallery.Orthogonal.Hard
