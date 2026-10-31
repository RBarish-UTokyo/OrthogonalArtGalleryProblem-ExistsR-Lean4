module

public import ArtGallery.Orthogonal.Hard.PinsAddLe
public import ArtGallery.Orthogonal.Hard.PinsAddLeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ
public import ArtGallery.Orthogonal.Hard.PinSplit

/-!
# Pin checks of the group `slot addLe`, part 13 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddLeP26_b : (gAddLeP26.T.cert (slotZ .addLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddLeP26_p : (gAddLeP26.T.cert (slotZ .addLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddLeP26I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP26H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddLeP26_j : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP26 0 1000 = true := by decide +kernel
/-- The pin check of `gAddLeP26`, from its parts. -/
theorem gAddLeP26_ok : pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP26 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddLeP26_b (n := 100000) (by decide +kernel) gAddLeP26_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddLeP26_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddLeP27_b : (gAddLeP27.T.cert (slotZ .addLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddLeP27_p : (gAddLeP27.T.cert (slotZ .addLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddLeP27I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP27H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddLeP27_j : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP27 0 1000 = true := by decide +kernel
/-- The pin check of `gAddLeP27`, from its parts. -/
theorem gAddLeP27_ok : pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP27 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddLeP27_b (n := 100000) (by decide +kernel) gAddLeP27_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddLeP27_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddLeP28_b : (gAddLeP28.T.cert (slotZ .addLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddLeP28_p : (gAddLeP28.T.cert (slotZ .addLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddLeP28I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP28H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddLeP28_j : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP28 0 1000 = true := by decide +kernel
/-- The pin check of `gAddLeP28`, from its parts. -/
theorem gAddLeP28_ok : pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP28 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddLeP28_b (n := 100000) (by decide +kernel) gAddLeP28_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddLeP28_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddLeP29_b : (gAddLeP29.T.cert (slotZ .addLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddLeP29_p : (gAddLeP29.T.cert (slotZ .addLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddLeP29I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP29H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddLeP29_j : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP29 0 1000 = true := by decide +kernel
/-- The pin check of `gAddLeP29`, from its parts. -/
theorem gAddLeP29_ok : pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP29 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddLeP29_b (n := 100000) (by decide +kernel) gAddLeP29_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddLeP29_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddLeP30_b : (gAddLeP30.T.cert (slotZ .addLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddLeP30_p : (gAddLeP30.T.cert (slotZ .addLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddLeP30I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP30H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddLeP30_j : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP30 0 1000 = true := by decide +kernel
/-- The pin check of `gAddLeP30`, from its parts. -/
theorem gAddLeP30_ok : pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP30 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddLeP30_b (n := 100000) (by decide +kernel) gAddLeP30_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddLeP30_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddLeP31_b : (gAddLeP31.T.cert (slotZ .addLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddLeP31_p : (gAddLeP31.T.cert (slotZ .addLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddLeP31I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP31H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddLeP31_j : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP31 0 1000 = true := by decide +kernel
/-- The pin check of `gAddLeP31`, from its parts. -/
theorem gAddLeP31_ok : pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP31 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddLeP31_b (n := 100000) (by decide +kernel) gAddLeP31_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddLeP31_j

end

end ArtGallery.Orthogonal.Hard
