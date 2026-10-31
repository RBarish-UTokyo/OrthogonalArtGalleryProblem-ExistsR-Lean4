module

public import ArtGallery.Orthogonal.Hard.PinsAddGe
public import ArtGallery.Orthogonal.Hard.PinsAddGeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ
public import ArtGallery.Orthogonal.Hard.PinSplit

/-!
# Pin checks of the group `slot addGe`, part 13 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddGeP32_b : (gAddGeP32.T.cert (slotZ .addGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddGeP32_p : (gAddGeP32.T.cert (slotZ .addGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddGeP32I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP32H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddGeP32_j : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP32 0 1000 = true := by decide +kernel
/-- The pin check of `gAddGeP32`, from its parts. -/
theorem gAddGeP32_ok : pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP32 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddGeP32_b (n := 100000) (by decide +kernel) gAddGeP32_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddGeP32_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddGeP33_b : (gAddGeP33.T.cert (slotZ .addGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddGeP33_p : (gAddGeP33.T.cert (slotZ .addGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddGeP33I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP33H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddGeP33_j : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP33 0 1000 = true := by decide +kernel
/-- The pin check of `gAddGeP33`, from its parts. -/
theorem gAddGeP33_ok : pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP33 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddGeP33_b (n := 100000) (by decide +kernel) gAddGeP33_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddGeP33_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddGeP34_b : (gAddGeP34.T.cert (slotZ .addGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddGeP34_p : (gAddGeP34.T.cert (slotZ .addGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddGeP34I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP34H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddGeP34_j : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP34 0 1000 = true := by decide +kernel
/-- The pin check of `gAddGeP34`, from its parts. -/
theorem gAddGeP34_ok : pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP34 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddGeP34_b (n := 100000) (by decide +kernel) gAddGeP34_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddGeP34_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddGeP35_b : (gAddGeP35.T.cert (slotZ .addGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddGeP35_p : (gAddGeP35.T.cert (slotZ .addGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddGeP35I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP35H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddGeP35_j : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP35 0 1000 = true := by decide +kernel
/-- The pin check of `gAddGeP35`, from its parts. -/
theorem gAddGeP35_ok : pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP35 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddGeP35_b (n := 100000) (by decide +kernel) gAddGeP35_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddGeP35_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddGeP36_b : (gAddGeP36.T.cert (slotZ .addGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddGeP36_p : (gAddGeP36.T.cert (slotZ .addGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddGeP36I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP36H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddGeP36_j : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP36 0 1000 = true := by decide +kernel
/-- The pin check of `gAddGeP36`, from its parts. -/
theorem gAddGeP36_ok : pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP36 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddGeP36_b (n := 100000) (by decide +kernel) gAddGeP36_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddGeP36_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddGeP37_b : (gAddGeP37.T.cert (slotZ .addGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddGeP37_p : (gAddGeP37.T.cert (slotZ .addGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddGeP37I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP37H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddGeP37_j : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP37 0 1000 = true := by decide +kernel
/-- The pin check of `gAddGeP37`, from its parts. -/
theorem gAddGeP37_ok : pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP37 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddGeP37_b (n := 100000) (by decide +kernel) gAddGeP37_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddGeP37_j

end

end ArtGallery.Orthogonal.Hard
