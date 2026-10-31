module

public import ArtGallery.Orthogonal.Hard.PinsAddGe
public import ArtGallery.Orthogonal.Hard.PinsAddGeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ
public import ArtGallery.Orthogonal.Hard.PinSplit

/-!
# Pin checks of the group `slot addGe`, part 15 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddGeP39_b : (gAddGeP39.T.cert (slotZ .addGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddGeP39_p : (gAddGeP39.T.cert (slotZ .addGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddGeP39I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP39H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddGeP39_j : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP39 0 1000 = true := by decide +kernel
/-- The pin check of `gAddGeP39`, from its parts. -/
theorem gAddGeP39_ok : pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP39 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddGeP39_b (n := 100000) (by decide +kernel) gAddGeP39_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddGeP39_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddGeP40_b : (gAddGeP40.T.cert (slotZ .addGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddGeP40_p : (gAddGeP40.T.cert (slotZ .addGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddGeP40I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP40H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddGeP40_j : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP40 0 1000 = true := by decide +kernel
/-- The pin check of `gAddGeP40`, from its parts. -/
theorem gAddGeP40_ok : pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP40 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddGeP40_b (n := 100000) (by decide +kernel) gAddGeP40_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddGeP40_j

end

end ArtGallery.Orthogonal.Hard
