module

public import ArtGallery.Orthogonal.Hard.PinsInvGe
public import ArtGallery.Orthogonal.Hard.PinSplit
public import ArtGallery.Orthogonal.Hard.PinsInvGeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ

/-!
# Pin checks of the group `slot invGe`, part 0 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gInvGeP0_b : (gInvGeP0.T.cert (slotZ .invGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gInvGeP0_p : (gInvGeP0.T.cert (slotZ .invGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gInvGeP0I rfl (slotZ .invGe) keysZInvGe_ok gInvGeP0H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gInvGeP0_j : pinJR (slotZ .invGe) gInvGeWs gInvGeRks gInvGeSps gInvGeP0 0 1000 = true := by decide +kernel
/-- The pin check of `gInvGeP0`, from its parts. -/
theorem gInvGeP0_ok : pinB (slotZ .invGe) gInvGeWs gInvGeRks gInvGeSps gInvGeP0 = true :=
  pinB_of_parts (LCert.ok_of_parts gInvGeP0_b (n := 100000) (by decide +kernel) gInvGeP0_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gInvGeP0_j


set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gInvGeP1_b : (gInvGeP1.T.cert (slotZ .invGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gInvGeP1_p : (gInvGeP1.T.cert (slotZ .invGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gInvGeP1I rfl (slotZ .invGe) keysZInvGe_ok gInvGeP1H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gInvGeP1_j : pinJR (slotZ .invGe) gInvGeWs gInvGeRks gInvGeSps gInvGeP1 0 1000 = true := by decide +kernel
/-- The pin check of `gInvGeP1`, from its parts. -/
theorem gInvGeP1_ok : pinB (slotZ .invGe) gInvGeWs gInvGeRks gInvGeSps gInvGeP1 = true :=
  pinB_of_parts (LCert.ok_of_parts gInvGeP1_b (n := 100000) (by decide +kernel) gInvGeP1_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gInvGeP1_j


set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gInvGeP2_b : (gInvGeP2.T.cert (slotZ .invGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gInvGeP2_p : (gInvGeP2.T.cert (slotZ .invGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gInvGeP2I rfl (slotZ .invGe) keysZInvGe_ok gInvGeP2H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gInvGeP2_j : pinJR (slotZ .invGe) gInvGeWs gInvGeRks gInvGeSps gInvGeP2 0 1000 = true := by decide +kernel
/-- The pin check of `gInvGeP2`, from its parts. -/
theorem gInvGeP2_ok : pinB (slotZ .invGe) gInvGeWs gInvGeRks gInvGeSps gInvGeP2 = true :=
  pinB_of_parts (LCert.ok_of_parts gInvGeP2_b (n := 100000) (by decide +kernel) gInvGeP2_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gInvGeP2_j


set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gInvGeP3_b : (gInvGeP3.T.cert (slotZ .invGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gInvGeP3_p : (gInvGeP3.T.cert (slotZ .invGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gInvGeP3I rfl (slotZ .invGe) keysZInvGe_ok gInvGeP3H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gInvGeP3_j : pinJR (slotZ .invGe) gInvGeWs gInvGeRks gInvGeSps gInvGeP3 0 1000 = true := by decide +kernel
/-- The pin check of `gInvGeP3`, from its parts. -/
theorem gInvGeP3_ok : pinB (slotZ .invGe) gInvGeWs gInvGeRks gInvGeSps gInvGeP3 = true :=
  pinB_of_parts (LCert.ok_of_parts gInvGeP3_b (n := 100000) (by decide +kernel) gInvGeP3_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gInvGeP3_j


set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gInvGeP4_b : (gInvGeP4.T.cert (slotZ .invGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gInvGeP4_p : (gInvGeP4.T.cert (slotZ .invGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gInvGeP4I rfl (slotZ .invGe) keysZInvGe_ok gInvGeP4H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gInvGeP4_j : pinJR (slotZ .invGe) gInvGeWs gInvGeRks gInvGeSps gInvGeP4 0 1000 = true := by decide +kernel
/-- The pin check of `gInvGeP4`, from its parts. -/
theorem gInvGeP4_ok : pinB (slotZ .invGe) gInvGeWs gInvGeRks gInvGeSps gInvGeP4 = true :=
  pinB_of_parts (LCert.ok_of_parts gInvGeP4_b (n := 100000) (by decide +kernel) gInvGeP4_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gInvGeP4_j


set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gInvGeP5_b : (gInvGeP5.T.cert (slotZ .invGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gInvGeP5_p : (gInvGeP5.T.cert (slotZ .invGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gInvGeP5I rfl (slotZ .invGe) keysZInvGe_ok gInvGeP5H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gInvGeP5_j : pinJR (slotZ .invGe) gInvGeWs gInvGeRks gInvGeSps gInvGeP5 0 1000 = true := by decide +kernel
/-- The pin check of `gInvGeP5`, from its parts. -/
theorem gInvGeP5_ok : pinB (slotZ .invGe) gInvGeWs gInvGeRks gInvGeSps gInvGeP5 = true :=
  pinB_of_parts (LCert.ok_of_parts gInvGeP5_b (n := 100000) (by decide +kernel) gInvGeP5_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gInvGeP5_j


end

end ArtGallery.Orthogonal.Hard
