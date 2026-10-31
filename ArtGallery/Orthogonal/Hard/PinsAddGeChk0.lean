module

public import ArtGallery.Orthogonal.Hard.PinsAddGe
public import ArtGallery.Orthogonal.Hard.PinsAddGeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ
public import ArtGallery.Orthogonal.Hard.PinSplit

/-!
# Pin checks of the group `slot addGe`, part 0 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddGeP0_b : (gAddGeP0.T.cert (slotZ .addGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddGeP0_p : (gAddGeP0.T.cert (slotZ .addGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddGeP0I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP0H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddGeP0_j : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP0 0 1000 = true := by decide +kernel
/-- The pin check of `gAddGeP0`, from its parts. -/
theorem gAddGeP0_ok : pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP0 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddGeP0_b (n := 100000) (by decide +kernel) gAddGeP0_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddGeP0_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddGeP1_b : (gAddGeP1.T.cert (slotZ .addGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddGeP1_p : (gAddGeP1.T.cert (slotZ .addGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddGeP1I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP1H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddGeP1_j : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP1 0 1000 = true := by decide +kernel
/-- The pin check of `gAddGeP1`, from its parts. -/
theorem gAddGeP1_ok : pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP1 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddGeP1_b (n := 100000) (by decide +kernel) gAddGeP1_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddGeP1_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddGeP2_b : (gAddGeP2.T.cert (slotZ .addGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddGeP2_p : (gAddGeP2.T.cert (slotZ .addGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddGeP2I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP2H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddGeP2_j : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP2 0 1000 = true := by decide +kernel
/-- The pin check of `gAddGeP2`, from its parts. -/
theorem gAddGeP2_ok : pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP2 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddGeP2_b (n := 100000) (by decide +kernel) gAddGeP2_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddGeP2_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddGeP3_b : (gAddGeP3.T.cert (slotZ .addGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddGeP3_p : (gAddGeP3.T.cert (slotZ .addGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddGeP3I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP3H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddGeP3_j : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP3 0 1000 = true := by decide +kernel
/-- The pin check of `gAddGeP3`, from its parts. -/
theorem gAddGeP3_ok : pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP3 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddGeP3_b (n := 100000) (by decide +kernel) gAddGeP3_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddGeP3_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddGeP4_b : (gAddGeP4.T.cert (slotZ .addGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddGeP4_p : (gAddGeP4.T.cert (slotZ .addGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddGeP4I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP4H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddGeP4_j : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP4 0 1000 = true := by decide +kernel
/-- The pin check of `gAddGeP4`, from its parts. -/
theorem gAddGeP4_ok : pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP4 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddGeP4_b (n := 100000) (by decide +kernel) gAddGeP4_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddGeP4_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddGeP5_b : (gAddGeP5.T.cert (slotZ .addGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddGeP5_p : (gAddGeP5.T.cert (slotZ .addGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddGeP5I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP5H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddGeP5_j : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP5 0 1000 = true := by decide +kernel
/-- The pin check of `gAddGeP5`, from its parts. -/
theorem gAddGeP5_ok : pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP5 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddGeP5_b (n := 100000) (by decide +kernel) gAddGeP5_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddGeP5_j

end

end ArtGallery.Orthogonal.Hard
