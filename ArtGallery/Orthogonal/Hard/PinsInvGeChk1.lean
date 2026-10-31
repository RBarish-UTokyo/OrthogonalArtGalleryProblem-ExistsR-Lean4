module

public import ArtGallery.Orthogonal.Hard.PinsInvGe
public import ArtGallery.Orthogonal.Hard.PinSplit
public import ArtGallery.Orthogonal.Hard.PinsInvGeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ

/-!
# Pin checks of the group `slot invGe`, part 1 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gInvGeP6_b : (gInvGeP6.T.cert (slotZ .invGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gInvGeP6_p : (gInvGeP6.T.cert (slotZ .invGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gInvGeP6I rfl (slotZ .invGe) keysZInvGe_ok gInvGeP6H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gInvGeP6_j : pinJR (slotZ .invGe) gInvGeWs gInvGeRks gInvGeSps gInvGeP6 0 1000 = true := by decide +kernel
/-- The pin check of `gInvGeP6`, from its parts. -/
theorem gInvGeP6_ok : pinB (slotZ .invGe) gInvGeWs gInvGeRks gInvGeSps gInvGeP6 = true :=
  pinB_of_parts (LCert.ok_of_parts gInvGeP6_b (n := 100000) (by decide +kernel) gInvGeP6_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gInvGeP6_j


set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gInvGeP7_b : (gInvGeP7.T.cert (slotZ .invGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gInvGeP7_p : (gInvGeP7.T.cert (slotZ .invGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gInvGeP7I rfl (slotZ .invGe) keysZInvGe_ok gInvGeP7H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gInvGeP7_j : pinJR (slotZ .invGe) gInvGeWs gInvGeRks gInvGeSps gInvGeP7 0 1000 = true := by decide +kernel
/-- The pin check of `gInvGeP7`, from its parts. -/
theorem gInvGeP7_ok : pinB (slotZ .invGe) gInvGeWs gInvGeRks gInvGeSps gInvGeP7 = true :=
  pinB_of_parts (LCert.ok_of_parts gInvGeP7_b (n := 100000) (by decide +kernel) gInvGeP7_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gInvGeP7_j


set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gInvGeP8_b : (gInvGeP8.T.cert (slotZ .invGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gInvGeP8_p : (gInvGeP8.T.cert (slotZ .invGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gInvGeP8I rfl (slotZ .invGe) keysZInvGe_ok gInvGeP8H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gInvGeP8_j : pinJR (slotZ .invGe) gInvGeWs gInvGeRks gInvGeSps gInvGeP8 0 1000 = true := by decide +kernel
/-- The pin check of `gInvGeP8`, from its parts. -/
theorem gInvGeP8_ok : pinB (slotZ .invGe) gInvGeWs gInvGeRks gInvGeSps gInvGeP8 = true :=
  pinB_of_parts (LCert.ok_of_parts gInvGeP8_b (n := 100000) (by decide +kernel) gInvGeP8_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gInvGeP8_j


set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gInvGeP9_b : (gInvGeP9.T.cert (slotZ .invGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gInvGeP9_p : (gInvGeP9.T.cert (slotZ .invGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gInvGeP9I rfl (slotZ .invGe) keysZInvGe_ok gInvGeP9H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gInvGeP9_j : pinJR (slotZ .invGe) gInvGeWs gInvGeRks gInvGeSps gInvGeP9 0 1000 = true := by decide +kernel
/-- The pin check of `gInvGeP9`, from its parts. -/
theorem gInvGeP9_ok : pinB (slotZ .invGe) gInvGeWs gInvGeRks gInvGeSps gInvGeP9 = true :=
  pinB_of_parts (LCert.ok_of_parts gInvGeP9_b (n := 100000) (by decide +kernel) gInvGeP9_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gInvGeP9_j


set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gInvGeP10_b : (gInvGeP10.T.cert (slotZ .invGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gInvGeP10_p : (gInvGeP10.T.cert (slotZ .invGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gInvGeP10I rfl (slotZ .invGe) keysZInvGe_ok gInvGeP10H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gInvGeP10_j : pinJR (slotZ .invGe) gInvGeWs gInvGeRks gInvGeSps gInvGeP10 0 1000 = true := by decide +kernel
/-- The pin check of `gInvGeP10`, from its parts. -/
theorem gInvGeP10_ok : pinB (slotZ .invGe) gInvGeWs gInvGeRks gInvGeSps gInvGeP10 = true :=
  pinB_of_parts (LCert.ok_of_parts gInvGeP10_b (n := 100000) (by decide +kernel) gInvGeP10_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gInvGeP10_j


set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gInvGeP11_b : (gInvGeP11.T.cert (slotZ .invGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gInvGeP11_p : (gInvGeP11.T.cert (slotZ .invGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gInvGeP11I rfl (slotZ .invGe) keysZInvGe_ok gInvGeP11H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gInvGeP11_j : pinJR (slotZ .invGe) gInvGeWs gInvGeRks gInvGeSps gInvGeP11 0 1000 = true := by decide +kernel
/-- The pin check of `gInvGeP11`, from its parts. -/
theorem gInvGeP11_ok : pinB (slotZ .invGe) gInvGeWs gInvGeRks gInvGeSps gInvGeP11 = true :=
  pinB_of_parts (LCert.ok_of_parts gInvGeP11_b (n := 100000) (by decide +kernel) gInvGeP11_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gInvGeP11_j


end

end ArtGallery.Orthogonal.Hard
