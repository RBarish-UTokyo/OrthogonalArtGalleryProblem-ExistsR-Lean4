module

public import ArtGallery.Orthogonal.Hard.PinsAddLe
public import ArtGallery.Orthogonal.Hard.PinsAddLeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ
public import ArtGallery.Orthogonal.Hard.PinSplit

/-!
# Pin checks of the group `slot addLe`, part 1 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddLeP6_b : (gAddLeP6.T.cert (slotZ .addLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddLeP6_p : (gAddLeP6.T.cert (slotZ .addLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddLeP6I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP6H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddLeP6_j : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP6 0 1000 = true := by decide +kernel
/-- The pin check of `gAddLeP6`, from its parts. -/
theorem gAddLeP6_ok : pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP6 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddLeP6_b (n := 100000) (by decide +kernel) gAddLeP6_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddLeP6_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddLeP7_b : (gAddLeP7.T.cert (slotZ .addLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddLeP7_p : (gAddLeP7.T.cert (slotZ .addLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddLeP7I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP7H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddLeP7_j : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP7 0 1000 = true := by decide +kernel
/-- The pin check of `gAddLeP7`, from its parts. -/
theorem gAddLeP7_ok : pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP7 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddLeP7_b (n := 100000) (by decide +kernel) gAddLeP7_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddLeP7_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddLeP8_b : (gAddLeP8.T.cert (slotZ .addLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddLeP8_p : (gAddLeP8.T.cert (slotZ .addLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddLeP8I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP8H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddLeP8_j : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP8 0 1000 = true := by decide +kernel
/-- The pin check of `gAddLeP8`, from its parts. -/
theorem gAddLeP8_ok : pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP8 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddLeP8_b (n := 100000) (by decide +kernel) gAddLeP8_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddLeP8_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddLeP9_b : (gAddLeP9.T.cert (slotZ .addLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddLeP9_p : (gAddLeP9.T.cert (slotZ .addLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddLeP9I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP9H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddLeP9_j : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP9 0 1000 = true := by decide +kernel
/-- The pin check of `gAddLeP9`, from its parts. -/
theorem gAddLeP9_ok : pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP9 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddLeP9_b (n := 100000) (by decide +kernel) gAddLeP9_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddLeP9_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddLeP10_b : (gAddLeP10.T.cert (slotZ .addLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddLeP10_p : (gAddLeP10.T.cert (slotZ .addLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddLeP10I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP10H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddLeP10_j : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP10 0 1000 = true := by decide +kernel
/-- The pin check of `gAddLeP10`, from its parts. -/
theorem gAddLeP10_ok : pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP10 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddLeP10_b (n := 100000) (by decide +kernel) gAddLeP10_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddLeP10_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddLeP11_b : (gAddLeP11.T.cert (slotZ .addLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddLeP11_p : (gAddLeP11.T.cert (slotZ .addLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddLeP11I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP11H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddLeP11_j : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP11 0 1000 = true := by decide +kernel
/-- The pin check of `gAddLeP11`, from its parts. -/
theorem gAddLeP11_ok : pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP11 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddLeP11_b (n := 100000) (by decide +kernel) gAddLeP11_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddLeP11_j

end

end ArtGallery.Orthogonal.Hard
