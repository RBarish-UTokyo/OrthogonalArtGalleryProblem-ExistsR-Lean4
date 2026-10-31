module

public import ArtGallery.Orthogonal.Hard.PinsInvRevLe
public import ArtGallery.Orthogonal.Hard.PinSplit
public import ArtGallery.Orthogonal.Hard.PinsInvRevLeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ

/-!
# Pin checks of the group `slot invRevLe`, part 0 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gInvRevLeP0_b : (gInvRevLeP0.T.cert (slotZ .invRevLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gInvRevLeP0_p : (gInvRevLeP0.T.cert (slotZ .invRevLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gInvRevLeP0I rfl (slotZ .invRevLe) keysZInvRevLe_ok gInvRevLeP0H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gInvRevLeP0_j : pinJR (slotZ .invRevLe) gInvRevLeWs gInvRevLeRks gInvRevLeSps gInvRevLeP0 0 1000 = true := by decide +kernel
/-- The pin check of `gInvRevLeP0`, from its parts. -/
theorem gInvRevLeP0_ok : pinB (slotZ .invRevLe) gInvRevLeWs gInvRevLeRks gInvRevLeSps gInvRevLeP0 = true :=
  pinB_of_parts (LCert.ok_of_parts gInvRevLeP0_b (n := 100000) (by decide +kernel) gInvRevLeP0_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gInvRevLeP0_j


set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gInvRevLeP1_b : (gInvRevLeP1.T.cert (slotZ .invRevLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gInvRevLeP1_p : (gInvRevLeP1.T.cert (slotZ .invRevLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gInvRevLeP1I rfl (slotZ .invRevLe) keysZInvRevLe_ok gInvRevLeP1H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gInvRevLeP1_j : pinJR (slotZ .invRevLe) gInvRevLeWs gInvRevLeRks gInvRevLeSps gInvRevLeP1 0 1000 = true := by decide +kernel
/-- The pin check of `gInvRevLeP1`, from its parts. -/
theorem gInvRevLeP1_ok : pinB (slotZ .invRevLe) gInvRevLeWs gInvRevLeRks gInvRevLeSps gInvRevLeP1 = true :=
  pinB_of_parts (LCert.ok_of_parts gInvRevLeP1_b (n := 100000) (by decide +kernel) gInvRevLeP1_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gInvRevLeP1_j


set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gInvRevLeP2_b : (gInvRevLeP2.T.cert (slotZ .invRevLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gInvRevLeP2_p : (gInvRevLeP2.T.cert (slotZ .invRevLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gInvRevLeP2I rfl (slotZ .invRevLe) keysZInvRevLe_ok gInvRevLeP2H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gInvRevLeP2_j : pinJR (slotZ .invRevLe) gInvRevLeWs gInvRevLeRks gInvRevLeSps gInvRevLeP2 0 1000 = true := by decide +kernel
/-- The pin check of `gInvRevLeP2`, from its parts. -/
theorem gInvRevLeP2_ok : pinB (slotZ .invRevLe) gInvRevLeWs gInvRevLeRks gInvRevLeSps gInvRevLeP2 = true :=
  pinB_of_parts (LCert.ok_of_parts gInvRevLeP2_b (n := 100000) (by decide +kernel) gInvRevLeP2_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gInvRevLeP2_j


set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gInvRevLeP3_b : (gInvRevLeP3.T.cert (slotZ .invRevLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gInvRevLeP3_p : (gInvRevLeP3.T.cert (slotZ .invRevLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gInvRevLeP3I rfl (slotZ .invRevLe) keysZInvRevLe_ok gInvRevLeP3H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gInvRevLeP3_j : pinJR (slotZ .invRevLe) gInvRevLeWs gInvRevLeRks gInvRevLeSps gInvRevLeP3 0 1000 = true := by decide +kernel
/-- The pin check of `gInvRevLeP3`, from its parts. -/
theorem gInvRevLeP3_ok : pinB (slotZ .invRevLe) gInvRevLeWs gInvRevLeRks gInvRevLeSps gInvRevLeP3 = true :=
  pinB_of_parts (LCert.ok_of_parts gInvRevLeP3_b (n := 100000) (by decide +kernel) gInvRevLeP3_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gInvRevLeP3_j


set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gInvRevLeP4_b : (gInvRevLeP4.T.cert (slotZ .invRevLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gInvRevLeP4_p : (gInvRevLeP4.T.cert (slotZ .invRevLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gInvRevLeP4I rfl (slotZ .invRevLe) keysZInvRevLe_ok gInvRevLeP4H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gInvRevLeP4_j : pinJR (slotZ .invRevLe) gInvRevLeWs gInvRevLeRks gInvRevLeSps gInvRevLeP4 0 1000 = true := by decide +kernel
/-- The pin check of `gInvRevLeP4`, from its parts. -/
theorem gInvRevLeP4_ok : pinB (slotZ .invRevLe) gInvRevLeWs gInvRevLeRks gInvRevLeSps gInvRevLeP4 = true :=
  pinB_of_parts (LCert.ok_of_parts gInvRevLeP4_b (n := 100000) (by decide +kernel) gInvRevLeP4_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gInvRevLeP4_j


set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gInvRevLeP5_b : (gInvRevLeP5.T.cert (slotZ .invRevLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gInvRevLeP5_p : (gInvRevLeP5.T.cert (slotZ .invRevLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gInvRevLeP5I rfl (slotZ .invRevLe) keysZInvRevLe_ok gInvRevLeP5H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gInvRevLeP5_j : pinJR (slotZ .invRevLe) gInvRevLeWs gInvRevLeRks gInvRevLeSps gInvRevLeP5 0 1000 = true := by decide +kernel
/-- The pin check of `gInvRevLeP5`, from its parts. -/
theorem gInvRevLeP5_ok : pinB (slotZ .invRevLe) gInvRevLeWs gInvRevLeRks gInvRevLeSps gInvRevLeP5 = true :=
  pinB_of_parts (LCert.ok_of_parts gInvRevLeP5_b (n := 100000) (by decide +kernel) gInvRevLeP5_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gInvRevLeP5_j


end

end ArtGallery.Orthogonal.Hard
