module

public import ArtGallery.Orthogonal.Hard.PinsAddLe
public import ArtGallery.Orthogonal.Hard.PinsAddLeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ
public import ArtGallery.Orthogonal.Hard.PinSplit

/-!
# Pin checks of the group `slot addLe`, part 7 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddLeP20_b : (gAddLeP20.T.cert (slotZ .addLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddLeP20_p : (gAddLeP20.T.cert (slotZ .addLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddLeP20I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP20H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddLeP20_j : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP20 0 1000 = true := by decide +kernel
/-- The pin check of `gAddLeP20`, from its parts. -/
theorem gAddLeP20_ok : pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP20 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddLeP20_b (n := 100000) (by decide +kernel) gAddLeP20_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddLeP20_j

end

end ArtGallery.Orthogonal.Hard
