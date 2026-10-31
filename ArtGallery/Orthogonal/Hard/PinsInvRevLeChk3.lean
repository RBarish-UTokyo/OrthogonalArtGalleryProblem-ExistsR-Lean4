module

public import ArtGallery.Orthogonal.Hard.PinsInvRevLe
public import ArtGallery.Orthogonal.Hard.PinSplit
public import ArtGallery.Orthogonal.Hard.PinsInvRevLeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ

/-!
# Pin checks of the group `slot invRevLe`, part 3 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gInvRevLeP18_b : (gInvRevLeP18.T.cert (slotZ .invRevLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gInvRevLeP18_p : (gInvRevLeP18.T.cert (slotZ .invRevLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gInvRevLeP18I rfl (slotZ .invRevLe) keysZInvRevLe_ok gInvRevLeP18H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gInvRevLeP18_j : pinJR (slotZ .invRevLe) gInvRevLeWs gInvRevLeRks gInvRevLeSps gInvRevLeP18 0 1000 = true := by decide +kernel
/-- The pin check of `gInvRevLeP18`, from its parts. -/
theorem gInvRevLeP18_ok : pinB (slotZ .invRevLe) gInvRevLeWs gInvRevLeRks gInvRevLeSps gInvRevLeP18 = true :=
  pinB_of_parts (LCert.ok_of_parts gInvRevLeP18_b (n := 100000) (by decide +kernel) gInvRevLeP18_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gInvRevLeP18_j


set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gInvRevLeP19_b : (gInvRevLeP19.T.cert (slotZ .invRevLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gInvRevLeP19_p : (gInvRevLeP19.T.cert (slotZ .invRevLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gInvRevLeP19I rfl (slotZ .invRevLe) keysZInvRevLe_ok gInvRevLeP19H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gInvRevLeP19_j : pinJR (slotZ .invRevLe) gInvRevLeWs gInvRevLeRks gInvRevLeSps gInvRevLeP19 0 1000 = true := by decide +kernel
/-- The pin check of `gInvRevLeP19`, from its parts. -/
theorem gInvRevLeP19_ok : pinB (slotZ .invRevLe) gInvRevLeWs gInvRevLeRks gInvRevLeSps gInvRevLeP19 = true :=
  pinB_of_parts (LCert.ok_of_parts gInvRevLeP19_b (n := 100000) (by decide +kernel) gInvRevLeP19_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gInvRevLeP19_j


set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gInvRevLeP20_b : (gInvRevLeP20.T.cert (slotZ .invRevLe)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gInvRevLeP20_p : (gInvRevLeP20.T.cert (slotZ .invRevLe)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gInvRevLeP20I rfl (slotZ .invRevLe) keysZInvRevLe_ok gInvRevLeP20H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gInvRevLeP20_j : pinJR (slotZ .invRevLe) gInvRevLeWs gInvRevLeRks gInvRevLeSps gInvRevLeP20 0 1000 = true := by decide +kernel
/-- The pin check of `gInvRevLeP20`, from its parts. -/
theorem gInvRevLeP20_ok : pinB (slotZ .invRevLe) gInvRevLeWs gInvRevLeRks gInvRevLeSps gInvRevLeP20 = true :=
  pinB_of_parts (LCert.ok_of_parts gInvRevLeP20_b (n := 100000) (by decide +kernel) gInvRevLeP20_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gInvRevLeP20_j


set_option maxRecDepth 100000 in
theorem gInvRevLeHQ_ok : gInvRevLeHQ.all (hqB (slotZ .invRevLe) gInvRevLeWs gInvRevLePs gInvRevLeSps) = true := by decide +kernel

end

end ArtGallery.Orthogonal.Hard
