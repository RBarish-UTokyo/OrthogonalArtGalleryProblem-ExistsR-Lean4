module

public import ArtGallery.Orthogonal.Hard.PinsAddGe
public import ArtGallery.Orthogonal.Hard.PinsAddGeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ
public import ArtGallery.Orthogonal.Hard.PinSplit

/-!
# Pin checks of the group `slot addGe`, part 9 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddGeP20_b : (gAddGeP20.T.cert (slotZ .addGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddGeP20_p : (gAddGeP20.T.cert (slotZ .addGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddGeP20I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP20H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddGeP20_j : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP20 0 1000 = true := by decide +kernel
/-- The pin check of `gAddGeP20`, from its parts. -/
theorem gAddGeP20_ok : pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP20 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddGeP20_b (n := 100000) (by decide +kernel) gAddGeP20_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddGeP20_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddGeP21_b : (gAddGeP21.T.cert (slotZ .addGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddGeP21_p : (gAddGeP21.T.cert (slotZ .addGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddGeP21I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP21H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddGeP21_j : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP21 0 1000 = true := by decide +kernel
/-- The pin check of `gAddGeP21`, from its parts. -/
theorem gAddGeP21_ok : pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP21 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddGeP21_b (n := 100000) (by decide +kernel) gAddGeP21_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddGeP21_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddGeP22_b : (gAddGeP22.T.cert (slotZ .addGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddGeP22_p : (gAddGeP22.T.cert (slotZ .addGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddGeP22I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP22H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddGeP22_j : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP22 0 1000 = true := by decide +kernel
/-- The pin check of `gAddGeP22`, from its parts. -/
theorem gAddGeP22_ok : pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP22 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddGeP22_b (n := 100000) (by decide +kernel) gAddGeP22_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddGeP22_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddGeP23_b : (gAddGeP23.T.cert (slotZ .addGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddGeP23_p : (gAddGeP23.T.cert (slotZ .addGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddGeP23I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP23H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddGeP23_j : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP23 0 1000 = true := by decide +kernel
/-- The pin check of `gAddGeP23`, from its parts. -/
theorem gAddGeP23_ok : pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP23 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddGeP23_b (n := 100000) (by decide +kernel) gAddGeP23_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddGeP23_j

end

end ArtGallery.Orthogonal.Hard
