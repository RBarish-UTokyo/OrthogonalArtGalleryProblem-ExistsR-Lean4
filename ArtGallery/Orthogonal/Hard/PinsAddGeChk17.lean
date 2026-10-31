module

public import ArtGallery.Orthogonal.Hard.PinsAddGe
public import ArtGallery.Orthogonal.Hard.PinsAddGeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ
public import ArtGallery.Orthogonal.Hard.PinSplit

/-!
# Pin checks of the group `slot addGe`, part 17 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddGeP42_b : (gAddGeP42.T.cert (slotZ .addGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddGeP42_p : (gAddGeP42.T.cert (slotZ .addGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddGeP42I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP42H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddGeP42_j : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP42 0 1000 = true := by decide +kernel
/-- The pin check of `gAddGeP42`, from its parts. -/
theorem gAddGeP42_ok : pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP42 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddGeP42_b (n := 100000) (by decide +kernel) gAddGeP42_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddGeP42_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddGeP43_b : (gAddGeP43.T.cert (slotZ .addGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddGeP43_p : (gAddGeP43.T.cert (slotZ .addGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddGeP43I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP43H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddGeP43_j : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP43 0 1000 = true := by decide +kernel
/-- The pin check of `gAddGeP43`, from its parts. -/
theorem gAddGeP43_ok : pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP43 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddGeP43_b (n := 100000) (by decide +kernel) gAddGeP43_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddGeP43_j

end

end ArtGallery.Orthogonal.Hard
