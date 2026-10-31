module

public import ArtGallery.Orthogonal.Hard.PinsAddLe
public import ArtGallery.Orthogonal.Hard.PinsAddLeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ
public import ArtGallery.Orthogonal.Hard.PinSplit

/-!
# Pin checks of the group `slot addLe`, part 18 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddLeP42_b : (gAddLeP42.T.cert (slotZ .addLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddLeP42_p : (gAddLeP42.T.cert (slotZ .addLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddLeP42I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP42H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddLeP42_j : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP42 0 1000 = true := by decide +kernel
/-- The pin check of `gAddLeP42`, from its parts. -/
theorem gAddLeP42_ok : pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP42 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddLeP42_b (n := 100000) (by decide +kernel) gAddLeP42_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddLeP42_j

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gAddLeP43_b : (gAddLeP43.T.cert (slotZ .addLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gAddLeP43_p : (gAddLeP43.T.cert (slotZ .addLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gAddLeP43I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP43H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gAddLeP43_j : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP43 0 1000 = true := by decide +kernel
/-- The pin check of `gAddLeP43`, from its parts. -/
theorem gAddLeP43_ok : pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP43 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddLeP43_b (n := 100000) (by decide +kernel) gAddLeP43_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gAddLeP43_j

end

end ArtGallery.Orthogonal.Hard
