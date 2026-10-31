module

public import ArtGallery.Orthogonal.Hard.PinsAddGe
public import ArtGallery.Orthogonal.Hard.PinsAddGeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ
public import ArtGallery.Orthogonal.Hard.PinSplit

/-!
# Pin checks of the group `slot addGe`, part 1 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddGeP6_b : (gAddGeP6.T.cert (slotZ .addGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddGeP6_p : (gAddGeP6.T.cert (slotZ .addGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddGeP6I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP6H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddGeP6_j : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP6 0 1000 = true := by decide +kernel
/-- The pin check of `gAddGeP6`, from its parts. -/
theorem gAddGeP6_ok : pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP6 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddGeP6_b (n := 100000) (by decide +kernel) gAddGeP6_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddGeP6_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddGeP7_b : (gAddGeP7.T.cert (slotZ .addGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddGeP7_p : (gAddGeP7.T.cert (slotZ .addGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddGeP7I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP7H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddGeP7_j : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP7 0 1000 = true := by decide +kernel
/-- The pin check of `gAddGeP7`, from its parts. -/
theorem gAddGeP7_ok : pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP7 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddGeP7_b (n := 100000) (by decide +kernel) gAddGeP7_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddGeP7_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddGeP8_b : (gAddGeP8.T.cert (slotZ .addGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddGeP8_p : (gAddGeP8.T.cert (slotZ .addGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddGeP8I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP8H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddGeP8_j : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP8 0 1000 = true := by decide +kernel
/-- The pin check of `gAddGeP8`, from its parts. -/
theorem gAddGeP8_ok : pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP8 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddGeP8_b (n := 100000) (by decide +kernel) gAddGeP8_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddGeP8_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddGeP9_b : (gAddGeP9.T.cert (slotZ .addGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddGeP9_p : (gAddGeP9.T.cert (slotZ .addGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddGeP9I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP9H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddGeP9_j : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP9 0 1000 = true := by decide +kernel
/-- The pin check of `gAddGeP9`, from its parts. -/
theorem gAddGeP9_ok : pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP9 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddGeP9_b (n := 100000) (by decide +kernel) gAddGeP9_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddGeP9_j

end

end ArtGallery.Orthogonal.Hard
