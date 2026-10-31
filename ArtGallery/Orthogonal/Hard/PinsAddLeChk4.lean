module

public import ArtGallery.Orthogonal.Hard.PinsAddLe
public import ArtGallery.Orthogonal.Hard.PinsAddLeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ
public import ArtGallery.Orthogonal.Hard.PinSplit

/-!
# Pin checks of the group `slot addLe`, part 4 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddLeP14_b : (gAddLeP14.T.cert (slotZ .addLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddLeP14_p : (gAddLeP14.T.cert (slotZ .addLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddLeP14I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP14H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddLeP14_j : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP14 0 1000 = true := by decide +kernel
/-- The pin check of `gAddLeP14`, from its parts. -/
theorem gAddLeP14_ok : pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP14 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddLeP14_b (n := 100000) (by decide +kernel) gAddLeP14_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddLeP14_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddLeP15_b : (gAddLeP15.T.cert (slotZ .addLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddLeP15_p : (gAddLeP15.T.cert (slotZ .addLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddLeP15I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP15H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddLeP15_j : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP15 0 1000 = true := by decide +kernel
/-- The pin check of `gAddLeP15`, from its parts. -/
theorem gAddLeP15_ok : pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP15 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddLeP15_b (n := 100000) (by decide +kernel) gAddLeP15_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddLeP15_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddLeP16_b : (gAddLeP16.T.cert (slotZ .addLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddLeP16_p : (gAddLeP16.T.cert (slotZ .addLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddLeP16I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP16H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddLeP16_j : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP16 0 1000 = true := by decide +kernel
/-- The pin check of `gAddLeP16`, from its parts. -/
theorem gAddLeP16_ok : pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP16 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddLeP16_b (n := 100000) (by decide +kernel) gAddLeP16_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddLeP16_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddLeP17_b : (gAddLeP17.T.cert (slotZ .addLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddLeP17_p : (gAddLeP17.T.cert (slotZ .addLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddLeP17I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP17H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddLeP17_j : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP17 0 1000 = true := by decide +kernel
/-- The pin check of `gAddLeP17`, from its parts. -/
theorem gAddLeP17_ok : pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP17 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddLeP17_b (n := 100000) (by decide +kernel) gAddLeP17_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddLeP17_j

end

end ArtGallery.Orthogonal.Hard
