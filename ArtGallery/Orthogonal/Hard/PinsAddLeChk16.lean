module

public import ArtGallery.Orthogonal.Hard.PinsAddLe
public import ArtGallery.Orthogonal.Hard.PinsAddLeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ
public import ArtGallery.Orthogonal.Hard.PinSplit

/-!
# Pin checks of the group `slot addLe`, part 16 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddLeP39_b : (gAddLeP39.T.cert (slotZ .addLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddLeP39_p : (gAddLeP39.T.cert (slotZ .addLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddLeP39I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP39H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddLeP39_j : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP39 0 1000 = true := by decide +kernel
/-- The pin check of `gAddLeP39`, from its parts. -/
theorem gAddLeP39_ok : pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP39 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddLeP39_b (n := 100000) (by decide +kernel) gAddLeP39_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddLeP39_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddLeP40_b : (gAddLeP40.T.cert (slotZ .addLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddLeP40_p : (gAddLeP40.T.cert (slotZ .addLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddLeP40I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP40H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddLeP40_j : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP40 0 1000 = true := by decide +kernel
/-- The pin check of `gAddLeP40`, from its parts. -/
theorem gAddLeP40_ok : pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP40 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddLeP40_b (n := 100000) (by decide +kernel) gAddLeP40_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddLeP40_j

end

end ArtGallery.Orthogonal.Hard
