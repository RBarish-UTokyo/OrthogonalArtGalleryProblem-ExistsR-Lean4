module

public import ArtGallery.Orthogonal.Hard.PinsInvRevLe
public import ArtGallery.Orthogonal.Hard.PinSplit
public import ArtGallery.Orthogonal.Hard.PinsInvRevLeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ

/-!
# Pin checks of the group `slot invRevLe`, part 1 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gInvRevLeP6_b : (gInvRevLeP6.T.cert (slotZ .invRevLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gInvRevLeP6_p : (gInvRevLeP6.T.cert (slotZ .invRevLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gInvRevLeP6I rfl (slotZ .invRevLe) keysZInvRevLe_ok gInvRevLeP6H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gInvRevLeP6_j : pinJR (slotZ .invRevLe) gInvRevLeWs gInvRevLeRks gInvRevLeSps gInvRevLeP6 0 1000 = true := by decide +kernel
/-- The pin check of `gInvRevLeP6`, from its parts. -/
theorem gInvRevLeP6_ok : pinB (slotZ .invRevLe) gInvRevLeWs gInvRevLeRks gInvRevLeSps gInvRevLeP6 = true :=
  pinB_of_parts (LCert.ok_of_parts gInvRevLeP6_b (n := 100000) (by decide +kernel) gInvRevLeP6_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gInvRevLeP6_j


set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gInvRevLeP7_b : (gInvRevLeP7.T.cert (slotZ .invRevLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gInvRevLeP7_p : (gInvRevLeP7.T.cert (slotZ .invRevLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gInvRevLeP7I rfl (slotZ .invRevLe) keysZInvRevLe_ok gInvRevLeP7H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gInvRevLeP7_j : pinJR (slotZ .invRevLe) gInvRevLeWs gInvRevLeRks gInvRevLeSps gInvRevLeP7 0 1000 = true := by decide +kernel
/-- The pin check of `gInvRevLeP7`, from its parts. -/
theorem gInvRevLeP7_ok : pinB (slotZ .invRevLe) gInvRevLeWs gInvRevLeRks gInvRevLeSps gInvRevLeP7 = true :=
  pinB_of_parts (LCert.ok_of_parts gInvRevLeP7_b (n := 100000) (by decide +kernel) gInvRevLeP7_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gInvRevLeP7_j


set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gInvRevLeP8_b : (gInvRevLeP8.T.cert (slotZ .invRevLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gInvRevLeP8_p : (gInvRevLeP8.T.cert (slotZ .invRevLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gInvRevLeP8I rfl (slotZ .invRevLe) keysZInvRevLe_ok gInvRevLeP8H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gInvRevLeP8_j : pinJR (slotZ .invRevLe) gInvRevLeWs gInvRevLeRks gInvRevLeSps gInvRevLeP8 0 1000 = true := by decide +kernel
/-- The pin check of `gInvRevLeP8`, from its parts. -/
theorem gInvRevLeP8_ok : pinB (slotZ .invRevLe) gInvRevLeWs gInvRevLeRks gInvRevLeSps gInvRevLeP8 = true :=
  pinB_of_parts (LCert.ok_of_parts gInvRevLeP8_b (n := 100000) (by decide +kernel) gInvRevLeP8_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gInvRevLeP8_j


set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gInvRevLeP9_b : (gInvRevLeP9.T.cert (slotZ .invRevLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gInvRevLeP9_p : (gInvRevLeP9.T.cert (slotZ .invRevLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gInvRevLeP9I rfl (slotZ .invRevLe) keysZInvRevLe_ok gInvRevLeP9H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gInvRevLeP9_j : pinJR (slotZ .invRevLe) gInvRevLeWs gInvRevLeRks gInvRevLeSps gInvRevLeP9 0 1000 = true := by decide +kernel
/-- The pin check of `gInvRevLeP9`, from its parts. -/
theorem gInvRevLeP9_ok : pinB (slotZ .invRevLe) gInvRevLeWs gInvRevLeRks gInvRevLeSps gInvRevLeP9 = true :=
  pinB_of_parts (LCert.ok_of_parts gInvRevLeP9_b (n := 100000) (by decide +kernel) gInvRevLeP9_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gInvRevLeP9_j


set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gInvRevLeP10_b : (gInvRevLeP10.T.cert (slotZ .invRevLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gInvRevLeP10_p : (gInvRevLeP10.T.cert (slotZ .invRevLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gInvRevLeP10I rfl (slotZ .invRevLe) keysZInvRevLe_ok gInvRevLeP10H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gInvRevLeP10_j : pinJR (slotZ .invRevLe) gInvRevLeWs gInvRevLeRks gInvRevLeSps gInvRevLeP10 0 1000 = true := by decide +kernel
/-- The pin check of `gInvRevLeP10`, from its parts. -/
theorem gInvRevLeP10_ok : pinB (slotZ .invRevLe) gInvRevLeWs gInvRevLeRks gInvRevLeSps gInvRevLeP10 = true :=
  pinB_of_parts (LCert.ok_of_parts gInvRevLeP10_b (n := 100000) (by decide +kernel) gInvRevLeP10_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gInvRevLeP10_j


set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gInvRevLeP11_b : (gInvRevLeP11.T.cert (slotZ .invRevLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gInvRevLeP11_p : (gInvRevLeP11.T.cert (slotZ .invRevLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gInvRevLeP11I rfl (slotZ .invRevLe) keysZInvRevLe_ok gInvRevLeP11H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gInvRevLeP11_j : pinJR (slotZ .invRevLe) gInvRevLeWs gInvRevLeRks gInvRevLeSps gInvRevLeP11 0 1000 = true := by decide +kernel
/-- The pin check of `gInvRevLeP11`, from its parts. -/
theorem gInvRevLeP11_ok : pinB (slotZ .invRevLe) gInvRevLeWs gInvRevLeRks gInvRevLeSps gInvRevLeP11 = true :=
  pinB_of_parts (LCert.ok_of_parts gInvRevLeP11_b (n := 100000) (by decide +kernel) gInvRevLeP11_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gInvRevLeP11_j


end

end ArtGallery.Orthogonal.Hard
