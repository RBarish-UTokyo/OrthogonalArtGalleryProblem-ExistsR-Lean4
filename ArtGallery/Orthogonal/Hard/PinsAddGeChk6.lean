module

public import ArtGallery.Orthogonal.Hard.PinsAddGe
public import ArtGallery.Orthogonal.Hard.PinsAddGeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ
public import ArtGallery.Orthogonal.Hard.PinSplit

/-!
# Pin checks of the group `slot addGe`, part 6 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddGeP14_b : (gAddGeP14.T.cert (slotZ .addGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddGeP14_p : (gAddGeP14.T.cert (slotZ .addGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddGeP14I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP14H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddGeP14_j : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP14 0 1000 = true := by decide +kernel
/-- The pin check of `gAddGeP14`, from its parts. -/
theorem gAddGeP14_ok : pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP14 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddGeP14_b (n := 100000) (by decide +kernel) gAddGeP14_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddGeP14_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddGeP15_b : (gAddGeP15.T.cert (slotZ .addGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddGeP15_p : (gAddGeP15.T.cert (slotZ .addGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddGeP15I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP15H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddGeP15_j : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP15 0 1000 = true := by decide +kernel
/-- The pin check of `gAddGeP15`, from its parts. -/
theorem gAddGeP15_ok : pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP15 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddGeP15_b (n := 100000) (by decide +kernel) gAddGeP15_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddGeP15_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddGeP16_b : (gAddGeP16.T.cert (slotZ .addGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddGeP16_p : (gAddGeP16.T.cert (slotZ .addGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddGeP16I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP16H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddGeP16_j : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP16 0 1000 = true := by decide +kernel
/-- The pin check of `gAddGeP16`, from its parts. -/
theorem gAddGeP16_ok : pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP16 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddGeP16_b (n := 100000) (by decide +kernel) gAddGeP16_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddGeP16_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddGeP17_b : (gAddGeP17.T.cert (slotZ .addGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddGeP17_p : (gAddGeP17.T.cert (slotZ .addGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddGeP17I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP17H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddGeP17_j : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP17 0 1000 = true := by decide +kernel
/-- The pin check of `gAddGeP17`, from its parts. -/
theorem gAddGeP17_ok : pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP17 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddGeP17_b (n := 100000) (by decide +kernel) gAddGeP17_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddGeP17_j

end

end ArtGallery.Orthogonal.Hard
