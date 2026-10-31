module

public import ArtGallery.Orthogonal.Hard.PinsInvGe
public import ArtGallery.Orthogonal.Hard.PinSplit
public import ArtGallery.Orthogonal.Hard.PinsInvGeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ

/-!
# Pin checks of the group `slot invGe`, part 2 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gInvGeP12_b : (gInvGeP12.T.cert (slotZ .invGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gInvGeP12_p : (gInvGeP12.T.cert (slotZ .invGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gInvGeP12I rfl (slotZ .invGe) keysZInvGe_ok gInvGeP12H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gInvGeP12_j : pinJR (slotZ .invGe) gInvGeWs gInvGeRks gInvGeSps gInvGeP12 0 1000 = true := by decide +kernel
/-- The pin check of `gInvGeP12`, from its parts. -/
theorem gInvGeP12_ok : pinB (slotZ .invGe) gInvGeWs gInvGeRks gInvGeSps gInvGeP12 = true :=
  pinB_of_parts (LCert.ok_of_parts gInvGeP12_b (n := 100000) (by decide +kernel) gInvGeP12_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gInvGeP12_j


set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gInvGeP13_b : (gInvGeP13.T.cert (slotZ .invGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gInvGeP13_p : (gInvGeP13.T.cert (slotZ .invGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gInvGeP13I rfl (slotZ .invGe) keysZInvGe_ok gInvGeP13H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gInvGeP13_j : pinJR (slotZ .invGe) gInvGeWs gInvGeRks gInvGeSps gInvGeP13 0 1000 = true := by decide +kernel
/-- The pin check of `gInvGeP13`, from its parts. -/
theorem gInvGeP13_ok : pinB (slotZ .invGe) gInvGeWs gInvGeRks gInvGeSps gInvGeP13 = true :=
  pinB_of_parts (LCert.ok_of_parts gInvGeP13_b (n := 100000) (by decide +kernel) gInvGeP13_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gInvGeP13_j


set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gInvGeP14_b : (gInvGeP14.T.cert (slotZ .invGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gInvGeP14_p : (gInvGeP14.T.cert (slotZ .invGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gInvGeP14I rfl (slotZ .invGe) keysZInvGe_ok gInvGeP14H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gInvGeP14_j : pinJR (slotZ .invGe) gInvGeWs gInvGeRks gInvGeSps gInvGeP14 0 1000 = true := by decide +kernel
/-- The pin check of `gInvGeP14`, from its parts. -/
theorem gInvGeP14_ok : pinB (slotZ .invGe) gInvGeWs gInvGeRks gInvGeSps gInvGeP14 = true :=
  pinB_of_parts (LCert.ok_of_parts gInvGeP14_b (n := 100000) (by decide +kernel) gInvGeP14_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gInvGeP14_j


set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gInvGeP15_b : (gInvGeP15.T.cert (slotZ .invGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gInvGeP15_p : (gInvGeP15.T.cert (slotZ .invGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gInvGeP15I rfl (slotZ .invGe) keysZInvGe_ok gInvGeP15H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gInvGeP15_j : pinJR (slotZ .invGe) gInvGeWs gInvGeRks gInvGeSps gInvGeP15 0 1000 = true := by decide +kernel
/-- The pin check of `gInvGeP15`, from its parts. -/
theorem gInvGeP15_ok : pinB (slotZ .invGe) gInvGeWs gInvGeRks gInvGeSps gInvGeP15 = true :=
  pinB_of_parts (LCert.ok_of_parts gInvGeP15_b (n := 100000) (by decide +kernel) gInvGeP15_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gInvGeP15_j


set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gInvGeP16_b : (gInvGeP16.T.cert (slotZ .invGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gInvGeP16_p : (gInvGeP16.T.cert (slotZ .invGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gInvGeP16I rfl (slotZ .invGe) keysZInvGe_ok gInvGeP16H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gInvGeP16_j : pinJR (slotZ .invGe) gInvGeWs gInvGeRks gInvGeSps gInvGeP16 0 1000 = true := by decide +kernel
/-- The pin check of `gInvGeP16`, from its parts. -/
theorem gInvGeP16_ok : pinB (slotZ .invGe) gInvGeWs gInvGeRks gInvGeSps gInvGeP16 = true :=
  pinB_of_parts (LCert.ok_of_parts gInvGeP16_b (n := 100000) (by decide +kernel) gInvGeP16_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gInvGeP16_j


set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gInvGeP17_b : (gInvGeP17.T.cert (slotZ .invGe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gInvGeP17_p : (gInvGeP17.T.cert (slotZ .invGe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gInvGeP17I rfl (slotZ .invGe) keysZInvGe_ok gInvGeP17H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gInvGeP17_j : pinJR (slotZ .invGe) gInvGeWs gInvGeRks gInvGeSps gInvGeP17 0 1000 = true := by decide +kernel
/-- The pin check of `gInvGeP17`, from its parts. -/
theorem gInvGeP17_ok : pinB (slotZ .invGe) gInvGeWs gInvGeRks gInvGeSps gInvGeP17 = true :=
  pinB_of_parts (LCert.ok_of_parts gInvGeP17_b (n := 100000) (by decide +kernel) gInvGeP17_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gInvGeP17_j


end

end ArtGallery.Orthogonal.Hard
