module

public import ArtGallery.Orthogonal.Hard.PinsAddLe
public import ArtGallery.Orthogonal.Hard.PinsAddLeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ
public import ArtGallery.Orthogonal.Hard.PinSplit

/-!
# Pin checks of the group `slot addLe`, part 10 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddLeP23_b : (gAddLeP23.T.cert (slotZ .addLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddLeP23_p : (gAddLeP23.T.cert (slotZ .addLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddLeP23I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP23H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddLeP23_j : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP23 0 1000 = true := by decide +kernel
/-- The pin check of `gAddLeP23`, from its parts. -/
theorem gAddLeP23_ok : pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP23 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddLeP23_b (n := 100000) (by decide +kernel) gAddLeP23_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddLeP23_j

end

end ArtGallery.Orthogonal.Hard
