module

public import ArtGallery.Orthogonal.Hard.PinsAddGe
public import ArtGallery.Orthogonal.Hard.PinsAddGeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ
public import ArtGallery.Orthogonal.Hard.PinSplit

/-!
# Pin checks of the group `slot addGe`, part 3 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddGeP11_b : (gAddGeP11.T.cert (slotZ .addGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddGeP11_p : (gAddGeP11.T.cert (slotZ .addGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddGeP11I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP11H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddGeP11_j : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP11 0 1000 = true := by decide +kernel
/-- The pin check of `gAddGeP11`, from its parts. -/
theorem gAddGeP11_ok : pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP11 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddGeP11_b (n := 100000) (by decide +kernel) gAddGeP11_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddGeP11_j

end

end ArtGallery.Orthogonal.Hard
