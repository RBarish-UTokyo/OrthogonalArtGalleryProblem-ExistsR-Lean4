module

public import ArtGallery.Orthogonal.Hard.PinsAddLe
public import ArtGallery.Orthogonal.Hard.PinsAddLeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ
public import ArtGallery.Orthogonal.Hard.PinSplit

/-!
# Pin checks of the group `slot addLe`, part 0 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddLeP0_b : (gAddLeP0.T.cert (slotZ .addLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddLeP0_p : (gAddLeP0.T.cert (slotZ .addLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddLeP0I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP0H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddLeP0_j : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP0 0 1000 = true := by decide +kernel
/-- The pin check of `gAddLeP0`, from its parts. -/
theorem gAddLeP0_ok : pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP0 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddLeP0_b (n := 100000) (by decide +kernel) gAddLeP0_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddLeP0_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddLeP1_b : (gAddLeP1.T.cert (slotZ .addLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddLeP1_p : (gAddLeP1.T.cert (slotZ .addLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddLeP1I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP1H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddLeP1_j : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP1 0 1000 = true := by decide +kernel
/-- The pin check of `gAddLeP1`, from its parts. -/
theorem gAddLeP1_ok : pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP1 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddLeP1_b (n := 100000) (by decide +kernel) gAddLeP1_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddLeP1_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddLeP2_b : (gAddLeP2.T.cert (slotZ .addLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddLeP2_p : (gAddLeP2.T.cert (slotZ .addLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddLeP2I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP2H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddLeP2_j : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP2 0 1000 = true := by decide +kernel
/-- The pin check of `gAddLeP2`, from its parts. -/
theorem gAddLeP2_ok : pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP2 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddLeP2_b (n := 100000) (by decide +kernel) gAddLeP2_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddLeP2_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddLeP3_b : (gAddLeP3.T.cert (slotZ .addLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddLeP3_p : (gAddLeP3.T.cert (slotZ .addLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddLeP3I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP3H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddLeP3_j : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP3 0 1000 = true := by decide +kernel
/-- The pin check of `gAddLeP3`, from its parts. -/
theorem gAddLeP3_ok : pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP3 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddLeP3_b (n := 100000) (by decide +kernel) gAddLeP3_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddLeP3_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddLeP4_b : (gAddLeP4.T.cert (slotZ .addLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddLeP4_p : (gAddLeP4.T.cert (slotZ .addLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddLeP4I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP4H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddLeP4_j : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP4 0 1000 = true := by decide +kernel
/-- The pin check of `gAddLeP4`, from its parts. -/
theorem gAddLeP4_ok : pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP4 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddLeP4_b (n := 100000) (by decide +kernel) gAddLeP4_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddLeP4_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddLeP5_b : (gAddLeP5.T.cert (slotZ .addLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddLeP5_p : (gAddLeP5.T.cert (slotZ .addLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddLeP5I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP5H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddLeP5_j : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP5 0 1000 = true := by decide +kernel
/-- The pin check of `gAddLeP5`, from its parts. -/
theorem gAddLeP5_ok : pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP5 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddLeP5_b (n := 100000) (by decide +kernel) gAddLeP5_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddLeP5_j

end

end ArtGallery.Orthogonal.Hard
