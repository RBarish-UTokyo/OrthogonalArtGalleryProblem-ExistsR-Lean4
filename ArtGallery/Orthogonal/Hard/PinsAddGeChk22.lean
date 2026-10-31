module

public import ArtGallery.Orthogonal.Hard.PinsAddGe
public import ArtGallery.Orthogonal.Hard.PinSplit

/-!
# Pin checks of the group `slot addGe`, part 22 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gAddGeHQ_ok : gAddGeHQ.all (hqB (slotZ .addGe) gAddGeWs gAddGePs gAddGeSps) = true := by decide +kernel

end

end ArtGallery.Orthogonal.Hard
