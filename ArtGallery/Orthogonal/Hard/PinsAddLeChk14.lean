module

public import ArtGallery.Orthogonal.Hard.PinsAddLe
public import ArtGallery.Orthogonal.Hard.PinsAddLeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ
public import ArtGallery.Orthogonal.Hard.PinSplit

/-!
# Pin checks of the group `slot addLe`, part 14 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddLeP32_b : (gAddLeP32.T.cert (slotZ .addLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddLeP32_p : (gAddLeP32.T.cert (slotZ .addLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddLeP32I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP32H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddLeP32_j : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP32 0 1000 = true := by decide +kernel
/-- The pin check of `gAddLeP32`, from its parts. -/
theorem gAddLeP32_ok : pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP32 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddLeP32_b (n := 100000) (by decide +kernel) gAddLeP32_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddLeP32_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddLeP33_b : (gAddLeP33.T.cert (slotZ .addLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddLeP33_p : (gAddLeP33.T.cert (slotZ .addLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddLeP33I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP33H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddLeP33_j : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP33 0 1000 = true := by decide +kernel
/-- The pin check of `gAddLeP33`, from its parts. -/
theorem gAddLeP33_ok : pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP33 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddLeP33_b (n := 100000) (by decide +kernel) gAddLeP33_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddLeP33_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddLeP34_b : (gAddLeP34.T.cert (slotZ .addLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddLeP34_p : (gAddLeP34.T.cert (slotZ .addLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddLeP34I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP34H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddLeP34_j : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP34 0 1000 = true := by decide +kernel
/-- The pin check of `gAddLeP34`, from its parts. -/
theorem gAddLeP34_ok : pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP34 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddLeP34_b (n := 100000) (by decide +kernel) gAddLeP34_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddLeP34_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddLeP35_b : (gAddLeP35.T.cert (slotZ .addLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddLeP35_p : (gAddLeP35.T.cert (slotZ .addLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddLeP35I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP35H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddLeP35_j : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP35 0 1000 = true := by decide +kernel
/-- The pin check of `gAddLeP35`, from its parts. -/
theorem gAddLeP35_ok : pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP35 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddLeP35_b (n := 100000) (by decide +kernel) gAddLeP35_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddLeP35_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddLeP36_b : (gAddLeP36.T.cert (slotZ .addLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddLeP36_p : (gAddLeP36.T.cert (slotZ .addLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddLeP36I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP36H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddLeP36_j : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP36 0 1000 = true := by decide +kernel
/-- The pin check of `gAddLeP36`, from its parts. -/
theorem gAddLeP36_ok : pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP36 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddLeP36_b (n := 100000) (by decide +kernel) gAddLeP36_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddLeP36_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddLeP37_b : (gAddLeP37.T.cert (slotZ .addLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddLeP37_p : (gAddLeP37.T.cert (slotZ .addLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddLeP37I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP37H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddLeP37_j : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP37 0 1000 = true := by decide +kernel
/-- The pin check of `gAddLeP37`, from its parts. -/
theorem gAddLeP37_ok : pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP37 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddLeP37_b (n := 100000) (by decide +kernel) gAddLeP37_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddLeP37_j

end

end ArtGallery.Orthogonal.Hard
