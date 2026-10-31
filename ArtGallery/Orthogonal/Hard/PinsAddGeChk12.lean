module

public import ArtGallery.Orthogonal.Hard.PinsAddGe
public import ArtGallery.Orthogonal.Hard.PinsAddGeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ
public import ArtGallery.Orthogonal.Hard.PinSplit

/-!
# Pin checks of the group `slot addGe`, part 12 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddGeP26_b : (gAddGeP26.T.cert (slotZ .addGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddGeP26_p : (gAddGeP26.T.cert (slotZ .addGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddGeP26I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP26H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddGeP26_j : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP26 0 1000 = true := by decide +kernel
/-- The pin check of `gAddGeP26`, from its parts. -/
theorem gAddGeP26_ok : pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP26 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddGeP26_b (n := 100000) (by decide +kernel) gAddGeP26_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddGeP26_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddGeP27_b : (gAddGeP27.T.cert (slotZ .addGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddGeP27_p : (gAddGeP27.T.cert (slotZ .addGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddGeP27I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP27H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddGeP27_j : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP27 0 1000 = true := by decide +kernel
/-- The pin check of `gAddGeP27`, from its parts. -/
theorem gAddGeP27_ok : pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP27 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddGeP27_b (n := 100000) (by decide +kernel) gAddGeP27_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddGeP27_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddGeP28_b : (gAddGeP28.T.cert (slotZ .addGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddGeP28_p : (gAddGeP28.T.cert (slotZ .addGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddGeP28I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP28H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddGeP28_j : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP28 0 1000 = true := by decide +kernel
/-- The pin check of `gAddGeP28`, from its parts. -/
theorem gAddGeP28_ok : pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP28 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddGeP28_b (n := 100000) (by decide +kernel) gAddGeP28_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddGeP28_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddGeP29_b : (gAddGeP29.T.cert (slotZ .addGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddGeP29_p : (gAddGeP29.T.cert (slotZ .addGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddGeP29I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP29H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddGeP29_j : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP29 0 1000 = true := by decide +kernel
/-- The pin check of `gAddGeP29`, from its parts. -/
theorem gAddGeP29_ok : pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP29 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddGeP29_b (n := 100000) (by decide +kernel) gAddGeP29_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddGeP29_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddGeP30_b : (gAddGeP30.T.cert (slotZ .addGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddGeP30_p : (gAddGeP30.T.cert (slotZ .addGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddGeP30I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP30H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddGeP30_j : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP30 0 1000 = true := by decide +kernel
/-- The pin check of `gAddGeP30`, from its parts. -/
theorem gAddGeP30_ok : pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP30 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddGeP30_b (n := 100000) (by decide +kernel) gAddGeP30_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddGeP30_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddGeP31_b : (gAddGeP31.T.cert (slotZ .addGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddGeP31_p : (gAddGeP31.T.cert (slotZ .addGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddGeP31I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP31H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddGeP31_j : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP31 0 1000 = true := by decide +kernel
/-- The pin check of `gAddGeP31`, from its parts. -/
theorem gAddGeP31_ok : pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP31 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddGeP31_b (n := 100000) (by decide +kernel) gAddGeP31_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddGeP31_j

end

end ArtGallery.Orthogonal.Hard
