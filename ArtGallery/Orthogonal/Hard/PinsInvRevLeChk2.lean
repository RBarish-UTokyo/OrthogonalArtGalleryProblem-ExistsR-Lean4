module

public import ArtGallery.Orthogonal.Hard.PinsInvRevLe
public import ArtGallery.Orthogonal.Hard.PinSplit
public import ArtGallery.Orthogonal.Hard.PinsInvRevLeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ

/-!
# Pin checks of the group `slot invRevLe`, part 2 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gInvRevLeP12_b : (gInvRevLeP12.T.cert (slotZ .invRevLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gInvRevLeP12_p : (gInvRevLeP12.T.cert (slotZ .invRevLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gInvRevLeP12I rfl (slotZ .invRevLe) keysZInvRevLe_ok gInvRevLeP12H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gInvRevLeP12_j : pinJR (slotZ .invRevLe) gInvRevLeWs gInvRevLeRks gInvRevLeSps gInvRevLeP12 0 1000 = true := by decide +kernel
/-- The pin check of `gInvRevLeP12`, from its parts. -/
theorem gInvRevLeP12_ok : pinB (slotZ .invRevLe) gInvRevLeWs gInvRevLeRks gInvRevLeSps gInvRevLeP12 = true :=
  pinB_of_parts (LCert.ok_of_parts gInvRevLeP12_b (n := 100000) (by decide +kernel) gInvRevLeP12_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gInvRevLeP12_j


set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gInvRevLeP13_b : (gInvRevLeP13.T.cert (slotZ .invRevLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gInvRevLeP13_p : (gInvRevLeP13.T.cert (slotZ .invRevLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gInvRevLeP13I rfl (slotZ .invRevLe) keysZInvRevLe_ok gInvRevLeP13H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gInvRevLeP13_j : pinJR (slotZ .invRevLe) gInvRevLeWs gInvRevLeRks gInvRevLeSps gInvRevLeP13 0 1000 = true := by decide +kernel
/-- The pin check of `gInvRevLeP13`, from its parts. -/
theorem gInvRevLeP13_ok : pinB (slotZ .invRevLe) gInvRevLeWs gInvRevLeRks gInvRevLeSps gInvRevLeP13 = true :=
  pinB_of_parts (LCert.ok_of_parts gInvRevLeP13_b (n := 100000) (by decide +kernel) gInvRevLeP13_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gInvRevLeP13_j


set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gInvRevLeP14_b : (gInvRevLeP14.T.cert (slotZ .invRevLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gInvRevLeP14_p : (gInvRevLeP14.T.cert (slotZ .invRevLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gInvRevLeP14I rfl (slotZ .invRevLe) keysZInvRevLe_ok gInvRevLeP14H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gInvRevLeP14_j : pinJR (slotZ .invRevLe) gInvRevLeWs gInvRevLeRks gInvRevLeSps gInvRevLeP14 0 1000 = true := by decide +kernel
/-- The pin check of `gInvRevLeP14`, from its parts. -/
theorem gInvRevLeP14_ok : pinB (slotZ .invRevLe) gInvRevLeWs gInvRevLeRks gInvRevLeSps gInvRevLeP14 = true :=
  pinB_of_parts (LCert.ok_of_parts gInvRevLeP14_b (n := 100000) (by decide +kernel) gInvRevLeP14_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gInvRevLeP14_j


set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gInvRevLeP15_b : (gInvRevLeP15.T.cert (slotZ .invRevLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gInvRevLeP15_p : (gInvRevLeP15.T.cert (slotZ .invRevLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gInvRevLeP15I rfl (slotZ .invRevLe) keysZInvRevLe_ok gInvRevLeP15H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gInvRevLeP15_j : pinJR (slotZ .invRevLe) gInvRevLeWs gInvRevLeRks gInvRevLeSps gInvRevLeP15 0 1000 = true := by decide +kernel
/-- The pin check of `gInvRevLeP15`, from its parts. -/
theorem gInvRevLeP15_ok : pinB (slotZ .invRevLe) gInvRevLeWs gInvRevLeRks gInvRevLeSps gInvRevLeP15 = true :=
  pinB_of_parts (LCert.ok_of_parts gInvRevLeP15_b (n := 100000) (by decide +kernel) gInvRevLeP15_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gInvRevLeP15_j


set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gInvRevLeP16_b : (gInvRevLeP16.T.cert (slotZ .invRevLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gInvRevLeP16_p : (gInvRevLeP16.T.cert (slotZ .invRevLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gInvRevLeP16I rfl (slotZ .invRevLe) keysZInvRevLe_ok gInvRevLeP16H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gInvRevLeP16_j : pinJR (slotZ .invRevLe) gInvRevLeWs gInvRevLeRks gInvRevLeSps gInvRevLeP16 0 1000 = true := by decide +kernel
/-- The pin check of `gInvRevLeP16`, from its parts. -/
theorem gInvRevLeP16_ok : pinB (slotZ .invRevLe) gInvRevLeWs gInvRevLeRks gInvRevLeSps gInvRevLeP16 = true :=
  pinB_of_parts (LCert.ok_of_parts gInvRevLeP16_b (n := 100000) (by decide +kernel) gInvRevLeP16_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gInvRevLeP16_j


set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gInvRevLeP17_b : (gInvRevLeP17.T.cert (slotZ .invRevLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gInvRevLeP17_p : (gInvRevLeP17.T.cert (slotZ .invRevLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gInvRevLeP17I rfl (slotZ .invRevLe) keysZInvRevLe_ok gInvRevLeP17H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gInvRevLeP17_j : pinJR (slotZ .invRevLe) gInvRevLeWs gInvRevLeRks gInvRevLeSps gInvRevLeP17 0 1000 = true := by decide +kernel
/-- The pin check of `gInvRevLeP17`, from its parts. -/
theorem gInvRevLeP17_ok : pinB (slotZ .invRevLe) gInvRevLeWs gInvRevLeRks gInvRevLeSps gInvRevLeP17 = true :=
  pinB_of_parts (LCert.ok_of_parts gInvRevLeP17_b (n := 100000) (by decide +kernel) gInvRevLeP17_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gInvRevLeP17_j


end

end ArtGallery.Orthogonal.Hard
